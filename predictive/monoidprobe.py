"""Is S_p represented, or only the predictive state?  (Project A.2)

    python -m predictive.monoidprobe runs/a2 --out results/a2

For each trained run from `lengthgen` this reads the residual stream on fresh
in-distribution sequences and reports three things.

Automaton extraction.  Cluster the final residuals with k-means and read off
an automaton: cluster(u) -> cluster(uo).  Reported: purity (clusters are
single predictive states), determinism (each cluster and symbol has one
successor cluster), whether the majority map from clusters to states
intertwines the extracted transitions with tau, and the share of residual
variance not explained by the predictive state (the excess).

Chunk probes.  For the last m symbols w, a linear readout of the element
tau_w of S_p from the residual at the end of w.  Two comparisons: the best
guess from the predictive states before and after w alone (what a pure state
tracker knows), and the same readout for a random regrouping of the words
with the same class sizes (what remembering the literal symbols gives).

Counterfactual probes.  A linear readout of tau_w(y) for states y the model
was not in before w, against the same two comparisons.

All readouts are least-squares classifiers onto one-hot labels, fitted on
half the sequences and scored on the other half.
"""

from __future__ import annotations

import argparse
import json
import statistics
from collections import defaultdict
from pathlib import Path

import torch

from .lengthgen import LGConfig, Machine, load

N_SEQ = 3000
CHUNK = {"act_a5": 8, "rrxor": 8}        # chunk length m; default below
DEFAULT_CHUNK = 6
RIDGE = 1e-2
N_CONTROLS = 5
KMEANS_K = (1, 2, 4)                      # multiples of the number of predictive states


# ---- data ---------------------------------------------------------------

def collect(cfg: LGConfig, mach: Machine, model, seed: int = 20_000):
    """Residuals on fresh training-length sequences.

    Returns tokens [N, L+1], states [N, L+1], and the residual stream
    [layers + 2, M, N, L+1, D]: embedding, after each block, and final-normed.
    """
    gen = torch.Generator().manual_seed(seed)
    x, s = mach.sample(N_SEQ, cfg.train_len, gen)
    off = torch.randint(0, cfg.max_pos - cfg.train_len - 1, (N_SEQ,), generator=gen)
    with torch.no_grad():
        _, final, stream = model.forward_all(x, off, layers=True)
    return x, s, torch.stack(stream + [final]).double()


def chunk_tables(mach: Machine, x, s, m: int):
    """One row per (sequence, position t >= m): the chunk, its element, states before and after."""
    N, L1 = x.shape
    ts = torch.arange(m, L1)
    words = torch.stack([x[:, t - m + 1:t + 1] for t in ts], 1).reshape(-1, m)     # symbols o_{t-m+1..t}
    seq = torch.arange(N)[:, None].expand(N, len(ts)).reshape(-1)
    pos = ts[None].expand(N, len(ts)).reshape(-1)
    before, after = s[seq, pos - m], s[seq, pos]
    images = torch.stack([mach.run(words, torch.full((len(words),), y)) for y in range(mach.n)], 1)
    code = (words * (mach.k ** torch.arange(m))).sum(1)                             # word id
    _, element = torch.unique(images, dim=0, return_inverse=True)
    return dict(seq=seq, pos=pos, before=before, after=after, images=images, word=code, element=element)


# ---- readouts -----------------------------------------------------------

def lstsq_acc(a_tr, y_tr, a_te, y_te, n_classes: int) -> float:
    """Test accuracy of a ridge least-squares classifier onto one-hot labels."""
    mu = a_tr.mean(0)
    a, b = a_tr - mu, a_te - mu
    scale = a.pow(2).mean().clamp_min(1e-12)
    onehot = torch.nn.functional.one_hot(y_tr, n_classes).double()
    bias = onehot.mean(0)
    w = torch.linalg.solve(a.T @ a + RIDGE * scale * len(a) * torch.eye(a.shape[1], dtype=a.dtype),
                           a.T @ (onehot - bias))
    return float(((b @ w + bias).argmax(1) == y_te).double().mean())


def lookup_acc(keys_tr, y_tr, keys_te, y_te) -> float:
    """Test accuracy of the best guess of the label from a discrete key (majority per key)."""
    table = defaultdict(lambda: defaultdict(int))
    for k, y in zip(keys_tr.tolist(), y_tr.tolist()):
        table[k][y] += 1
    overall = statistics.mode(y_tr.tolist())
    guess = torch.tensor([max(table[k], key=table[k].get) if k in table else overall
                          for k in keys_te.tolist()])
    return float((guess == y_te).double().mean())


def regroup(word, label, gen):
    """A random relabelling of words that keeps the number of words per label."""
    words, inv = torch.unique(word, return_inverse=True)
    lab_of_word = torch.zeros(len(words), dtype=torch.long).scatter_(0, inv, label)
    return lab_of_word[torch.randperm(len(words), generator=gen)][inv]


def chunk_probes(mach: Machine, x, s, stream, m: int) -> list[dict]:
    """Per model: element and counterfactual readouts at the best layer, with their comparisons."""
    tab = chunk_tables(mach, x, s, m)
    train = tab["seq"] < N_SEQ // 2
    test = ~train
    n_el = int(tab["element"].max()) + 1
    key_after = tab["after"]
    key_both = tab["before"] * (mach.n + 1) + tab["after"]
    gen = torch.Generator().manual_seed(0)
    controls = [regroup(tab["word"], tab["element"], gen) for _ in range(N_CONTROLS)]
    out = []
    for mi in range(stream.shape[1]):
        acts = [stream[layer, mi][tab["seq"], tab["pos"]] for layer in range(stream.shape[0])]
        el = [lstsq_acc(a[train], tab["element"][train], a[test], tab["element"][test], n_el) for a in acts]
        layer = max(range(len(el)), key=el.__getitem__)
        a = acts[layer]
        ctrl = [lstsq_acc(a[train], c[train], a[test], c[test], n_el) for c in controls]
        ctrl_best = [max(lstsq_acc(b[train], c[train], b[test], c[test], n_el) for b in acts)
                     for c in controls[:2]]
        # counterfactual: tau_w(y) for y different from the state before the chunk
        cf, cf_state, cf_ctrl = [], [], []
        perm = torch.randperm(len(tab["word"].unique()), generator=gen)
        words, inv = torch.unique(tab["word"], return_inverse=True)
        first = torch.zeros(len(words), dtype=torch.long).scatter_(0, inv, torch.arange(len(inv)))
        other = tab["images"][first[perm][inv]]                 # images under a randomly swapped word
        for y in range(mach.n):
            keep = tab["before"] != y
            tr, te = keep & train, keep & test
            lab = tab["images"][:, y]
            cf.append(lstsq_acc(a[tr], lab[tr], a[te], lab[te], mach.n + 1))
            cf_state.append(lookup_acc(key_both[tr], lab[tr], key_both[te], lab[te]))
            cf_ctrl.append(lstsq_acc(a[tr], other[:, y][tr], a[te], other[:, y][te], mach.n + 1))
        out.append(dict(
            model=mi, chunk=m, n_elements=n_el, n_words=len(words), layer=layer,
            element=el[layer], element_by_layer=el,
            element_from_after=lookup_acc(key_after[train], tab["element"][train],
                                          key_after[test], tab["element"][test]),
            element_from_states=lookup_acc(key_both[train], tab["element"][train],
                                           key_both[test], tab["element"][test]),
            element_regrouped=statistics.mean(ctrl), element_regrouped_best_layer=statistics.mean(ctrl_best),
            counterfactual=statistics.mean(cf), counterfactual_from_states=statistics.mean(cf_state),
            counterfactual_regrouped=statistics.mean(cf_ctrl),
            state=lstsq_acc(a[train], tab["after"][train], a[test], tab["after"][test], mach.n + 1),
        ))
    return out


# ---- automaton extraction -----------------------------------------------

def kmeans(a, k: int, gen, iters: int = 30):
    cent = a[torch.randint(len(a), (1,), generator=gen)]
    for _ in range(k - 1):                                    # k-means++ seeding
        d = torch.cdist(a, cent).min(1).values.pow(2)
        cent = torch.cat([cent, a[torch.multinomial(d / d.sum(), 1, generator=gen)]])
    for _ in range(iters):
        lab = torch.cdist(a, cent).argmin(1)
        for c in range(k):
            if (lab == c).any():
                cent[c] = a[lab == c].mean(0)
    return torch.cdist(a, cent).argmin(1)


def extraction(mach: Machine, x, s, final) -> list[dict]:
    """Per model and cluster count: purity, determinism, intertwining with tau, monoid size."""
    N, L1 = x.shape
    gen = torch.Generator().manual_seed(0)
    out = []
    for mi in range(final.shape[0]):
        a = final[mi][:, 1:].reshape(-1, final.shape[-1])     # positions 1..L
        st = s[:, 1:].reshape(-1)
        total = (a - a.mean(0)).pow(2).sum()
        within = sum((a[st == q] - a[st == q].mean(0)).pow(2).sum() for q in st.unique())
        rec = dict(model=mi, excess_variance=float(within / total), by_k=[])
        for mult in KMEANS_K:
            k = mult * mach.n
            lab = kmeans(a, k, gen).view(N, L1 - 1)
            flat = lab.reshape(-1)
            major = torch.stack([torch.bincount(st[flat == c], minlength=mach.n + 1).argmax()
                                 for c in range(k)])
            purity = float((major[flat] == st).double().mean())
            src, sym, dst = lab[:, :-1].reshape(-1), x[:, 2:].reshape(-1), lab[:, 1:].reshape(-1)
            counts = torch.zeros(k, mach.k, k).index_put_((src, sym, dst), torch.ones(len(src)),
                                                          accumulate=True)
            delta = counts.argmax(2)                           # extracted transition function
            seen = counts.sum(2) > 0
            determinism = float(counts.max(2).values.sum() / counts.sum())
            ok = (major[delta] == mach.step.cpu()[major][:, :mach.k]) & seen
            weight = counts.sum(2)
            intertwine = float((weight * ok).sum() / weight.sum())
            # monoid generated by the extracted maps, capped
            gens = [tuple(delta[:, o].tolist()) for o in range(mach.k)]
            els, queue = {tuple(range(k))}, [tuple(range(k))]
            while queue and len(els) <= 5000:
                t = queue.pop()
                for g in gens:
                    nxt = tuple(g[i] for i in t)
                    if nxt not in els:
                        els.add(nxt)
                        queue.append(nxt)
            rec["by_k"].append(dict(k=k, purity=purity, determinism=determinism, intertwine=intertwine,
                                    monoid_size=len(els) if len(els) <= 5000 else None))
        out.append(rec)
    return out


# ---- driver -------------------------------------------------------------

def analyse(path: Path, steps=(None,)) -> list[dict]:
    recs = []
    for step in steps:
        cfg, mach, model = load(path, step)
        x, s, stream = collect(cfg, mach, model)
        m = CHUNK.get(cfg.process, DEFAULT_CHUNK)
        probes = chunk_probes(mach, x, s, stream, m)
        ext = extraction(mach, x, s, stream[-1]) if step is None else [{}] * len(probes)
        for p, e in zip(probes, ext):
            recs.append({"process": cfg.process, "depth": cfg.n_layers, "width": cfg.d_model,
                         "step": cfg.steps if step is None else step, **p, **e})
    return recs


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("dir", type=Path)
    ap.add_argument("--out", type=Path, default=Path("results/a2"))
    ap.add_argument("--only", nargs="*", default=None)
    ap.add_argument("--timing", action="store_true", help="also probe every saved checkpoint")
    a = ap.parse_args()
    recs = []
    for p in sorted(a.dir.glob("*.jsonl")):
        if a.only and not any(p.name.startswith(o) for o in a.only):
            continue
        cfg = LGConfig(**json.loads(p.open().readline())["config"])
        steps = (None,) + (tuple(cfg.ckpt_steps) if a.timing else ())
        recs += analyse(p, steps)
        print(f"probed {p.name}", flush=True)
    a.out.mkdir(parents=True, exist_ok=True)
    (a.out / "probes.json").write_text(json.dumps(recs))


if __name__ == "__main__":
    main()
