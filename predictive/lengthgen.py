"""Length generalisation of next-symbol prediction (Project A.2).

    python -m predictive.lengthgen sweep --out runs/a2 [--only act_a5]
    python -m predictive.lengthgen long --out runs/a2long

A model reads BOS followed by symbols sampled from a process and is trained,
at every position, to predict the next symbol.  Training sequences have
`train_len` symbols; evaluation sequences have `test_len`.  Positions are
shifted by a random offset in training so that every positional embedding is
trained, and BOS marks where the sequence starts.

The exact next-symbol law at each position comes from the predictive machine,
so the reported loss is the KL divergence from the exact predictor, split by
position: up to the training length, and beyond it.  It is divided by the
same divergence for the best predictor that ignores the history.

This is length generalisation only.  Nothing here measures grokking.
"""

from __future__ import annotations

import argparse
import json
import math
import time
from dataclasses import asdict, dataclass
from pathlib import Path

import torch
import torch.nn.functional as F

from .processes import ACTIONS, get
from .train import StackedTransformer, pick_device

# width per depth, chosen so that depth * width^2 is about constant
WIDTH = {1: 128, 2: 92, 4: 64, 6: 52}
PROCESSES = list(ACTIONS) + ["z1r", "rrxor"]


@dataclass
class LGConfig:
    process: str
    n_layers: int
    d_model: int
    n_heads: int = 4
    seeds: int = 4
    train_len: int = 16
    test_len: int = 64
    max_pos: int = 96
    batch: int = 256
    steps: int = 30000
    lr: float = 1e-3
    wd: float = 0.1
    warmup: int = 500
    log_every: int = 500
    n_eval: int = 2048
    init_seed: int = 0
    ckpt_steps: tuple = (500, 1000, 2000, 5000, 10000, 20000)


class Machine:
    """The predictive machine as tensors: a sampler and the exact next-symbol law."""

    def __init__(self, process: str, device: str = "cpu"):
        pm = get(process).predictive_machine()
        assert pm.complete
        self.n, self.k = len(pm), len(pm.step[0])
        dead = self.n
        self.step = torch.tensor(
            [[dead if j is None else j for j in row] for row in pm.step] + [[dead] * self.k],
            dtype=torch.long, device=device)
        cond = [[float(c) for c in row] for row in pm.cond] + [[1.0 / self.k] * self.k]
        self.cond = torch.tensor(cond, dtype=torch.float32, device=device)
        self.device = device

    def sample(self, n: int, length: int, gen: torch.Generator):
        """Tokens [n, length + 1] starting with BOS (id k), and the state at each position."""
        s = torch.zeros(n, dtype=torch.long, device=self.device)
        toks = [torch.full((n,), self.k, dtype=torch.long, device=self.device)]
        states = [s]
        for _ in range(length):
            o = torch.multinomial(self.cond[s], 1, generator=gen).squeeze(1)
            s = self.step[s, o]
            toks.append(o)
            states.append(s)
        return torch.stack(toks, 1), torch.stack(states, 1)

    def run(self, words: torch.Tensor, start: torch.Tensor | None = None) -> torch.Tensor:
        """State after reading each row of `words` [n, m] from `start` (default the initial state)."""
        s = torch.zeros(len(words), dtype=torch.long, device=words.device) if start is None else start
        for t in range(words.shape[1]):
            s = self.step.to(words.device)[s, words[:, t]]
        return s


class SeqTransformer(StackedTransformer):
    """The stacked transformer, read at every position, with shifted positions."""

    def forward_all(self, x, offsets=None, layers=False):
        """x: [N, L] tokens.  Returns logits [M, N, L, out] and the final residual [M, N, L, D].

        With `layers`, also the residual stream after the embedding and after each block.
        """
        M, (N, L), H = self.tok.shape[0], x.shape, self.n_heads
        idx = torch.arange(L, device=x.device).expand(N, L)
        if offsets is not None:
            idx = idx + offsets[:, None]
        h = self.tok[:, x] + self.pos[:, idx]
        D = h.shape[-1]
        stream = [h]
        for p in self.layers:
            a = self._norm(h, p["g1"], p["b1"])
            q, k, v = torch.einsum("mnld,mde->mnle", a, p["qkv"]).split(D, dim=-1)
            q, k, v = (t.reshape(M, N, L, H, D // H).transpose(2, 3) for t in (q, k, v))
            att = (q @ k.transpose(-1, -2)) / math.sqrt(D // H)
            att = att.masked_fill(self.mask[:L, :L], float("-inf")).softmax(-1)
            o = (att @ v).transpose(2, 3).reshape(M, N, L, D)
            h = h + torch.einsum("mnld,mde->mnle", o, p["out"])
            a = self._norm(h, p["g2"], p["b2"])
            u = torch.einsum("mnld,mde->mnle", a, p["up"]) + p["up_b"][:, None, None, :]
            h = h + torch.einsum("mnle,med->mnld", F.gelu(u), p["down"])
            stream.append(h)
        final = self._norm(h, self.gf, self.bf)
        logits = torch.einsum("mnld,mdv->mnlv", final, self.unembed)
        return (logits, final, stream) if layers else (logits, final)


def build(cfg: LGConfig, k: int, device: str) -> SeqTransformer:
    return SeqTransformer(cfg.seeds, k + 1, cfg.max_pos, cfg.d_model, cfg.n_layers, cfg.n_heads,
                          4 * cfg.d_model, cfg.init_seed, n_out=k).to(device)


def load(path: Path, step: int | None = None, device: str = "cpu"):
    """Config, machine and model of a finished run (final weights, or a checkpoint step)."""
    meta = json.loads(path.open().readline())
    cfg = LGConfig(**meta["config"])
    mach = Machine(cfg.process, device)
    model = build(cfg, mach.k, device)
    saved = torch.load(path.with_suffix(".ckpt.pt"), map_location=device)
    model.load_state_dict(saved[cfg.steps if step is None else step])
    return cfg, mach, model.eval()


def kl_by_position(logits, cond):
    """KL(exact || model) per model and position: logits [M, N, L, k], cond [N, L, k]."""
    logq = F.log_softmax(logits, -1)
    logp = cond.clamp_min(1e-30).log()
    return (cond * (logp - logq)).sum(-1).mean(1)


def evaluate(model, mach: Machine, cfg: LGConfig, seed: int = 10_000):
    gen = torch.Generator(device=mach.device).manual_seed(seed)
    x, s = mach.sample(cfg.n_eval, cfg.test_len, gen)
    off = torch.randint(0, cfg.max_pos - cfg.test_len, (cfg.n_eval,), generator=gen, device=mach.device)
    cond = mach.cond[s]
    with torch.no_grad():
        kl = torch.cat([kl_by_position(model.forward_all(x[i:i + 512], off[i:i + 512])[0], cond[i:i + 512])
                        [None] for i in range(0, cfg.n_eval, 512)]).mean(0)   # [M, L + 1]
    marg = cond.mean(0, keepdim=True)                                          # history-free predictor
    base = (cond * (cond.clamp_min(1e-30).log() - marg.clamp_min(1e-30).log())).sum(-1).mean(0)
    return kl, base


def buckets(cfg: LGConfig):
    t = cfg.train_len
    return {"in": (1, t + 1), "x2": (t + 1, 2 * t + 1), "x4": (2 * t + 1, cfg.test_len + 1)}


def train(cfg: LGConfig, out: Path, device: str | None = None) -> None:
    device = device or pick_device()
    mach = Machine(cfg.process, device)
    model = build(cfg, mach.k, device)
    decayed = model.decayed()
    opt = torch.optim.Adam(model.parameters(), lr=cfg.lr)
    gen = torch.Generator(device=device).manual_seed(cfg.init_seed + 1)
    out.parent.mkdir(parents=True, exist_ok=True)
    fh = out.open("w")
    fh.write(json.dumps(dict(kind="meta", config=asdict(cfg), n_states=mach.n, k=mach.k, device=device,
                             n_params_per_model=sum(p.numel() for p in model.parameters()) // cfg.seeds))
             + "\n")
    ckpts = {}
    L = cfg.train_len
    for step in range(cfg.steps + 1):
        if step % cfg.log_every == 0 or step == cfg.steps:
            kl, base = evaluate(model, mach, cfg)
            for m in range(cfg.seeds):
                row = dict(kind="log", step=step, model=m)
                for name, (a, b) in buckets(cfg).items():
                    row[name] = kl[m, a:b].mean().item()
                    row[name + "_base"] = base[a:b].mean().item()
                fh.write(json.dumps(row) + "\n")
            fh.flush()
        if step in cfg.ckpt_steps or step == cfg.steps:
            ckpts[step] = {k: v.detach().cpu().clone() for k, v in model.state_dict().items()}
        if step == cfg.steps:
            break
        x, _ = mach.sample(cfg.batch, L, gen)
        off = torch.randint(0, cfg.max_pos - L, (cfg.batch,), generator=gen, device=device)
        logits, _ = model.forward_all(x[:, :-1], off)
        loss = F.cross_entropy(logits.reshape(-1, mach.k), x[:, 1:].expand(cfg.seeds, -1, -1).reshape(-1),
                               reduction="none").view(cfg.seeds, -1).mean(1)
        lr = cfg.lr * min(1.0, (step + 1) / cfg.warmup)
        for g in opt.param_groups:
            g["lr"] = lr
        opt.zero_grad(set_to_none=True)
        loss.sum().backward()
        opt.step()
        with torch.no_grad():
            for p in decayed:
                p.mul_(1 - lr * cfg.wd)
    fh.close()
    torch.save(ckpts, out.with_suffix(".ckpt.pt"))


def sweep() -> dict:
    return {f"{p}_d{depth}": LGConfig(p, depth, WIDTH[depth]) for p in PROCESSES for depth in WIDTH}


def long() -> dict:
    """Four times the trained length of `sweep`, for the group processes and one aperiodic control."""
    return {f"{p}_d{depth}_L64": LGConfig(p, depth, WIDTH[depth], train_len=64, test_len=256, max_pos=384)
            for p in ("act_s3", "act_s4", "act_a5", "act_ap5") for depth in (2, 6)}


def finished(path: Path, steps: int) -> bool:
    if not path.exists() or not path.with_suffix(".ckpt.pt").exists():
        return False
    return any(json.loads(line).get("step") == steps for line in path.open() if '"log"' in line)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("sweep", choices=["sweep", "long"])
    ap.add_argument("--out", type=Path, required=True)
    ap.add_argument("--device", default=None)
    ap.add_argument("--steps", type=int, default=None)
    ap.add_argument("--only", nargs="*", default=None)
    a = ap.parse_args()
    for name, cfg in (sweep() if a.sweep == "sweep" else long()).items():
        if a.only and not any(name.startswith(o) for o in a.only):
            continue
        if a.steps:
            cfg.steps = a.steps
            cfg.ckpt_steps = tuple(s for s in cfg.ckpt_steps if s < a.steps)
        path = a.out / f"{name}.jsonl"
        if finished(path, cfg.steps):
            print(f"skip {path}", flush=True)
            continue
        t = time.time()
        train(cfg, path, a.device)
        print(f"done {path}: {cfg.seeds} models, {time.time() - t:.0f}s", flush=True)


if __name__ == "__main__":
    main()
