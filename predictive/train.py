"""Full-batch training of many small transformers in parallel.

Every model sees the same enumerated contexts but has its own train /
held-out split, weight decay and initialisation.  The models are stacked along
a leading dimension and trained in one forward pass, so a sweep over fractions,
weight decays and seeds costs one run.

The loss is the KL divergence from the exact next-symbol law to the model's
prediction at the final position only, averaged uniformly over contexts.

    python -m predictive.train --process mod5 --length 4 \
        --frac 0.3 0.5 --wd 0.3 1.0 --seeds 2 --steps 5000 --out runs/mod5.jsonl
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import random
from dataclasses import asdict, dataclass, field
from pathlib import Path

import torch
import torch.nn.functional as F

from .dataset import ContextSet, enumerate_contexts
from .processes import get


@dataclass
class ModelSpec:
    """Settings that differ between the stacked models."""

    frac: float
    wd: float
    seed: int
    shuffle_targets: bool = False  # control: targets permuted across contexts


@dataclass
class TrainConfig:
    process: str
    length: int
    d_model: int = 64
    n_layers: int = 2
    n_heads: int = 4
    d_mlp: int = 256
    lr: float = 1e-3
    steps: int = 5000
    log_every: int = 50
    init_seed: int = 0
    horizon: int = 1  # target is the law of the next `horizon` symbols
    loss: str = "kl"  # "kl": softmax head; "mse": linear head, squared error on standardised probabilities
    models: list = field(default_factory=list)


class StackedTransformer(torch.nn.Module):
    """M independent pre-norm causal transformers with shared shape.

    Every parameter has a leading dimension M.  Models never interact, so the
    sum of their losses trains each one exactly as it would train alone.
    """

    def __init__(self, n_models, vocab, length, d_model, n_layers, n_heads, d_mlp, seed, n_out=None):
        super().__init__()
        assert d_model % n_heads == 0
        self.n_heads = n_heads
        gen = torch.Generator().manual_seed(seed)
        M, D = n_models, d_model

        def w(*shape, fan_in):
            return torch.nn.Parameter(torch.randn(M, *shape, generator=gen) / math.sqrt(fan_in))

        def zeros(*shape):
            return torch.nn.Parameter(torch.zeros(M, *shape))

        def ones(*shape):
            return torch.nn.Parameter(torch.ones(M, *shape))

        self.tok = w(vocab, D, fan_in=D)
        self.pos = w(length, D, fan_in=D)
        self.layers = torch.nn.ModuleList()
        for _ in range(n_layers):
            self.layers.append(torch.nn.ParameterDict(dict(
                g1=ones(D), b1=zeros(D),
                qkv=w(D, 3 * D, fan_in=D), out=w(D, D, fan_in=D),
                g2=ones(D), b2=zeros(D),
                up=w(D, d_mlp, fan_in=D), up_b=zeros(d_mlp),
                down=w(d_mlp, D, fan_in=d_mlp),
            )))
        self.gf, self.bf = ones(D), zeros(D)
        self.unembed = w(D, n_out or vocab, fan_in=D)
        self.register_buffer("mask", torch.triu(torch.ones(length, length, dtype=torch.bool), 1))

    def decayed(self):
        """Weight matrices and embeddings: the parameters weight decay acts on."""
        names = ("tok", "pos", "unembed", "qkv", "out", "up", "down")
        return [p for n, p in self.named_parameters() if n.split(".")[-1] in names]

    @staticmethod
    def _norm(h, g, b):
        h = h - h.mean(-1, keepdim=True)
        h = h / (h.pow(2).mean(-1, keepdim=True) + 1e-5).sqrt()
        return h * g[:, None, None, :] + b[:, None, None, :]

    def forward(self, x, return_residual=False):
        """x: [N, L] token ids.  Returns final-position logits [M, N, vocab]."""
        M, (N, L), H = self.tok.shape[0], x.shape, self.n_heads
        h = self.tok[:, x] + self.pos[:, None, :L]  # [M, N, L, D]
        D = h.shape[-1]
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
        last = self._norm(h, self.gf, self.bf)[:, :, -1]  # [M, N, D]
        logits = torch.einsum("mnd,mdv->mnv", last, self.unembed)
        return (logits, last) if return_residual else logits


def tensors(cs: ContextSet, device):
    x = torch.tensor(cs.contexts, dtype=torch.long, device=device)
    y = torch.tensor([[float(p) for p in t] for t in cs.targets], dtype=torch.float32, device=device)
    return x, y


def future_targets(g, cs: ContextSet, horizon: int, device):
    """Exact law of the next `horizon` symbols after each context, [N, k**horizon].

    The matrix of these laws over all contexts has rank at most the Hankel
    rank d, and reaches d once the horizon is long enough.
    """
    import itertools

    from .linalg import dot

    futures = list(itertools.product(range(g.k), repeat=horizon))
    rows = []
    for w in cs.contexts:
        eta = g.forward(w)
        z = dot(eta, g.final)
        rows.append([float(dot(g.forward(v, start=eta), g.final) / z) for v in futures])
    return torch.tensor(rows, dtype=torch.float32, device=device)


def mse_per_context(out, y):
    """Squared error between a linear output and the target law, summed over outcomes."""
    return (out - y).pow(2).sum(-1)


def kl_per_context(logits, y):
    """KL(y || softmax(logits)) for each model and context.  y: [M, N, V] or [N, V]."""
    logq = F.log_softmax(logits, dim=-1)
    ent = torch.where(y > 0, y * torch.log(y.clamp_min(1e-30)), torch.zeros_like(y)).sum(-1)
    return ent - (y * logq).sum(-1)


def effective_rank(resid):
    """Participation ratio of the centred final-position activations, per model.

    resid: [M, N, D].  Returns (sum s^2)^2 / sum s^4 over singular values s,
    which is 1 for a rank-one cloud and D for an isotropic one.
    """
    c = (resid - resid.mean(1, keepdim=True)).double()
    # squared singular values, from the small D x D Gram matrix (much faster than an SVD)
    s2 = torch.linalg.eigvalsh(c.transpose(1, 2) @ c).clamp_min(0)
    return (s2.sum(-1).pow(2) / s2.pow(2).sum(-1).clamp_min(1e-30)).float()


def state_probe(resid, state_ids, n_states, train_mask, ridge=1e-3):
    """Linear probe for the predictive state, per model.

    A ridge regression from final-position activations to the one-hot state is
    fitted on each model's training contexts.  Returns its accuracy on the
    training contexts and on the held-out contexts, each [M].
    """
    M, N, D = resid.shape
    x = torch.cat([resid, torch.ones(M, N, 1, device=resid.device)], -1).double()
    y = F.one_hot(state_ids, n_states).double().expand(M, N, n_states)
    w = train_mask.double().unsqueeze(-1)
    xw = x * w
    gram = xw.transpose(1, 2) @ x + ridge * torch.eye(D + 1, device=x.device, dtype=x.dtype)
    coef = torch.linalg.solve(gram, xw.transpose(1, 2) @ y)
    hit = ((x @ coef).argmax(-1) == state_ids).float()
    held = ~train_mask
    acc = lambda mask: (hit * mask).sum(1) / mask.sum(1).clamp_min(1)
    return acc(train_mask), acc(held)


def pick_device() -> str:
    if torch.cuda.is_available():
        return "cuda"
    return "cpu"


def train(
    cfg: TrainConfig, out: Path | None = None, device: str | None = None,
    save_steps: tuple = (), save_every: int = 0,
) -> list[dict]:
    """Train the stacked models and return the log rows.

    With `out` set, rows are also written as JSON lines.  Final-position
    activations of every model at each step in `save_steps` are saved next to
    it as `<out>.acts.pt`.
    """
    device = device or pick_device()
    cs = enumerate_contexts(get(cfg.process), cfg.length)
    x, y = tensors(cs, device)
    if cfg.horizon > 1:
        y = future_targets(get(cfg.process), cs, cfg.horizon, device)
    if cfg.loss == "mse":
        # drop outcomes that never vary and put the rest on a common scale;
        # without this the fit stalls for thousands of steps at the last-symbol solution.
        # The rank of the target matrix becomes d - 1, the constant direction going to the bias.
        y = y[:, y.std(0) > 0]
        y = (y - y.mean(0)) / y.std(0)
    per_context = mse_per_context if cfg.loss == "mse" else kl_per_context
    N, M = len(cs), len(cfg.models)
    state_ids = torch.tensor(cs.state_ids, dtype=torch.long, device=device)
    n_state_ids = max(cs.state_ids) + 1
    saved = {}

    train_mask = torch.zeros(M, N, dtype=torch.bool, device=device)
    targets = y.expand(M, N, -1).clone()
    for m, spec in enumerate(cfg.models):
        if spec.frac >= 1:
            train_mask[m] = True
        else:
            train_mask[m, cs.split(spec.frac, spec.seed)[0]] = True
        if spec.shuffle_targets:
            perm = list(range(N))
            random.Random(spec.seed + 1).shuffle(perm)
            targets[m] = y[perm]
    held_mask = ~train_mask
    wd = torch.tensor([s.wd for s in cfg.models], dtype=torch.float32, device=device)

    model = StackedTransformer(
        M, cs.alphabet, cfg.length, cfg.d_model, cfg.n_layers, cfg.n_heads, cfg.d_mlp, cfg.init_seed,
        n_out=y.shape[-1],
    ).to(device)
    opt = torch.optim.Adam(model.parameters(), lr=cfg.lr)
    decayed = model.decayed()

    # loss of the best context-independent prediction, the mean target:
    # held-out loss only shows generalisation once it is below this
    if cfg.loss == "mse":
        baseline = mse_per_context(y.mean(0).expand(N, -1), y).mean().item()
    else:
        baseline = kl_per_context(torch.log(y.mean(0).clamp_min(1e-30)).expand(N, -1), y).mean().item()
    meta = dict(
        kind="meta", config=asdict(cfg), n_contexts=N, n_states=cs.n_states,
        n_distinct_targets=cs.n_distinct_targets, device=device, baseline_kl=baseline,
        n_state_ids=n_state_ids,
        n_params_per_model=sum(p.numel() for p in model.parameters()) // M,
    )
    rows = [meta]
    fh = None
    if out is not None:
        out.parent.mkdir(parents=True, exist_ok=True)
        fh = out.open("w")
        fh.write(json.dumps(meta) + "\n")

    def masked_mean(v, mask):
        return (v * mask).sum(1) / mask.sum(1).clamp_min(1)

    for step in range(cfg.steps + 1):
        logits, resid = model(x, return_residual=True)
        kl = per_context(logits, targets)  # [M, N]
        train_loss = masked_mean(kl, train_mask)
        if step % cfg.log_every == 0 or step == cfg.steps:
            with torch.no_grad():
                held = masked_mean(kl, held_mask)
                # held-out loss is always against the true targets
                held_true = masked_mean(per_context(logits, y), held_mask)
                norm = sum(p.pow(2).flatten(1).sum(1) for p in decayed).sqrt()
                if device == "mps":  # no float64 there: do the diagnostics on the CPU
                    erank = effective_rank(resid.cpu())
                    probe_tr, probe_he = state_probe(resid.cpu(), state_ids.cpu(), n_state_ids, train_mask.cpu())
                else:
                    erank = effective_rank(resid)
                    probe_tr, probe_he = state_probe(resid, state_ids, n_state_ids, train_mask)
            for m in range(M):
                row = dict(
                    kind="log", step=step, model=m, train=train_loss[m].item(),
                    heldout=(held_true[m].item() if held_mask[m].any() else None),
                    heldout_vs_given=(held[m].item() if held_mask[m].any() else None),
                    weight_norm=norm[m].item(), erank=erank[m].item(),
                    probe_train=probe_tr[m].item(),
                    probe_heldout=(probe_he[m].item() if held_mask[m].any() else None),
                )
                rows.append(row)
                if fh:
                    fh.write(json.dumps(row) + "\n")
            if fh:
                fh.flush()
        if step in save_steps or (save_every and step % save_every == 0):
            saved[step] = resid.detach().half().cpu()
        if step == cfg.steps:
            break
        opt.zero_grad(set_to_none=True)
        train_loss.sum().backward()
        opt.step()
        with torch.no_grad():  # decoupled weight decay, per model
            for p in decayed:
                p.mul_((1 - cfg.lr * wd).view(M, *[1] * (p.dim() - 1)))
    if fh:
        fh.close()
    if saved and out is not None:
        torch.save(
            dict(acts=saved, state_ids=state_ids.cpu(), train_mask=train_mask.cpu(),
                 contexts=x.cpu()),
            out.with_suffix(".acts.pt"),
        )
    return rows


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--process", required=True)
    ap.add_argument("--length", type=int, required=True)
    ap.add_argument("--frac", type=float, nargs="+", default=[0.5])
    ap.add_argument("--wd", type=float, nargs="+", default=[1.0])
    ap.add_argument("--seeds", type=int, default=1)
    ap.add_argument("--shuffle-control", action="store_true",
                    help="add one shuffled-target model per (frac, wd)")
    ap.add_argument("--steps", type=int, default=5000)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--d-model", type=int, default=64)
    ap.add_argument("--layers", type=int, default=2)
    ap.add_argument("--heads", type=int, default=4)
    ap.add_argument("--log-every", type=int, default=50)
    ap.add_argument("--out", type=Path, default=None)
    ap.add_argument("--device", default=None)
    a = ap.parse_args()

    models = [ModelSpec(f, w, s) for f, w, s in itertools.product(a.frac, a.wd, range(a.seeds))]
    if a.shuffle_control:
        models += [ModelSpec(f, w, 0, True) for f, w in itertools.product(a.frac, a.wd)]
    cfg = TrainConfig(
        a.process, a.length, d_model=a.d_model, n_layers=a.layers, n_heads=a.heads,
        d_mlp=4 * a.d_model, lr=a.lr, steps=a.steps, log_every=a.log_every, models=models,
    )
    rows = train(cfg, a.out, a.device)
    meta = rows[0]
    print(f"{meta['n_contexts']} contexts, {meta['n_distinct_targets']} distinct targets, "
          f"{meta['n_params_per_model']} parameters per model, device {meta['device']}, "
          f"constant-prediction baseline {meta['baseline_kl']:.4f}")
    last = [r for r in rows if r["kind"] == "log" and r["step"] == cfg.steps]
    for r, spec in zip(last, models):
        held = "-" if r["heldout"] is None else f"{r['heldout']:.4f}"
        tag = " shuffled" if spec.shuffle_targets else ""
        print(f"frac {spec.frac:<5} wd {spec.wd:<5} seed {spec.seed}{tag}: "
              f"train {r['train']:.5f}  heldout {held}")


if __name__ == "__main__":
    main()
