"""Tables and the headline figure for Project A.2.

    python -m predictive.a2report runs/a2 --probes results/a2/probes.json --long runs/a2long --out results/a2
"""

from __future__ import annotations

import argparse
import json
import statistics
from collections import defaultdict
from pathlib import Path

from . import monoid
from .processes import get

CLASS = {"act_ap5": "aperiodic", "z1r": "aperiodic", "act_latch": "aperiodic, no reset word", "act_latch4": "aperiodic, no reset word",
         "act_latchwalk": "aperiodic, no reset word", "act_z6": "abelian group", "act_s3": "solvable group",
         "act_s4": "solvable group", "rrxor": "contains Z_3", "act_a5": "non-solvable group"}
NAME = {"act_ap5": "clamped walk", "z1r": "Z1R", "act_latch": "latched process", "act_latch4": "four-way latch",
        "act_latchwalk": "walk latch", "act_z6": "Z2 x Z3", "act_s3": "S3", "act_s4": "S4", "rrxor": "RRXOR", "act_a5": "A5"}
ORDER = ["act_ap5", "z1r", "act_latch", "act_latch4", "act_latchwalk", "act_z6", "act_s3", "act_s4", "rrxor", "act_a5"]
BUCKETS = ("in", "x2", "x4")


def med(xs):
    xs = [x for x in xs if x is not None]
    return statistics.median(xs) if xs else None


def load_runs(d: Path) -> list[dict]:
    """One record per model: final normalised loss in each position bucket, and its history."""
    out = []
    for p in sorted(d.glob("*.jsonl")):
        rows = [json.loads(line) for line in p.open()]
        cfg = rows[0]["config"]
        by = defaultdict(list)
        for r in rows[1:]:
            by[r["model"]].append(r)
        for m, rs in by.items():
            last = rs[-1]
            out.append(dict(
                process=cfg["process"], depth=cfg["n_layers"], width=cfg["d_model"], model=m,
                params=rows[0]["n_params_per_model"], train_len=cfg["train_len"],
                **{b: last[b] / last[b + "_base"] for b in BUCKETS},
                history=[(r["step"], *(r[b] / r[b + "_base"] for b in BUCKETS)) for r in rs],
            ))
    return out


def invariants() -> dict:
    out = {}
    for p in ORDER:
        pm = get(p).predictive_machine()
        ms = monoid.summarise(pm)
        out[p] = dict(states=len(pm), monoid=ms.size, aperiodic=ms.aperiodic)
    return out


def lg_table(runs) -> str:
    inv = invariants()
    depths = sorted({r["depth"] for r in runs})
    cols = ["process", "class", "\\|X_p\\|", "\\|S_p\\|"] + [f"depth {d}" for d in depths]
    lines = ["| " + " | ".join(cols) + " |", "|" + "---|" * len(cols)]
    for p in ORDER:
        if not any(r["process"] == p for r in runs):
            continue
        cells = []
        for d in depths:
            rs = [r for r in runs if r["process"] == p and r["depth"] == d]
            cells.append("-" if not rs else " / ".join(f"{med(r[b] for r in rs):.3f}" for b in BUCKETS))
        lines.append("| " + " | ".join([p, CLASS[p], str(inv[p]["states"]), str(inv[p]["monoid"])] + cells) + " |")
    return "\n".join(lines)


def probe_table(probes, depth: int) -> str:
    cols = ["process", "chunk", "elements", "state", "element", "from states", "regrouped",
            "counterfactual", "from states ", "regrouped ", "excess variance",
            "purity", "determinism", "intertwines"]
    lines = ["| " + " | ".join(cols) + " |", "|" + "---|" * len(cols)]
    for p in ORDER:
        rs = [r for r in probes if r["process"] == p and r["depth"] == depth and "by_k" in r]
        if not rs:
            continue
        f = lambda key: f"{med(r[key] for r in rs):.2f}"
        k1 = lambda key: f"{med(r['by_k'][0][key] for r in rs):.2f}"
        lines.append("| " + " | ".join([
            p, str(rs[0]["chunk"]), str(rs[0]["n_elements"]), f("state"), f("element"),
            f("element_from_states"), f("element_regrouped"), f("counterfactual"),
            f("counterfactual_from_states"), f("counterfactual_regrouped"), f("excess_variance"),
            k1("purity"), k1("determinism"), k1("intertwine")]) + " |")
    return "\n".join(lines)


def figure(runs, out: Path) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    depths = sorted({r["depth"] for r in runs})
    colours = {"aperiodic": "#2a7f62", "aperiodic, no reset word": "#d98c1f", "abelian group": "#3b6fb6", "solvable group": "#3b6fb6",
               "contains Z_3": "#8a6fb0", "non-solvable group": "#c0392b"}
    styles = {"act_ap5": "-", "z1r": "--", "act_latch": "-", "act_latch4": "--", "act_latchwalk": ":", "act_z6": ":", "act_s3": "-", "act_s4": "--", "rrxor": "-",
              "act_a5": "-"}
    fig, axes = plt.subplots(1, 3, figsize=(11, 3.9), sharey=True)
    titles = {"in": "positions 1 to 16 (trained)", "x2": "positions 17 to 32", "x4": "positions 33 to 64"}
    for ax, b in zip(axes, BUCKETS):
        for p in ORDER:
            ys = [med(r[b] for r in runs if r["process"] == p and r["depth"] == d) for d in depths]
            if any(y is None for y in ys):
                continue
            ax.plot(range(len(depths)), ys, styles[p], color=colours[CLASS[p]], marker="o", ms=4, lw=2,
                    label=f"{NAME[p]} ({CLASS[p]})")
        ax.axhline(1, color="0.6", lw=1)
        ax.set_yscale("log")
        ax.set_xticks(range(len(depths)), [str(d) for d in depths])
        ax.set_xlabel("depth (parameter count held about fixed)")
        ax.set_title(titles[b], fontsize=10)
        ax.grid(alpha=0.25, which="both")
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
    axes[0].set_ylabel("loss / loss of history-free predictor")
    fig.tight_layout(rect=(0, 0.13, 1, 1))
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, fontsize=7.5, frameon=False, loc="lower center", ncol=4)
    fig.savefig(out / "length_generalisation.png", dpi=160)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("dir", type=Path)
    ap.add_argument("--probes", type=Path, default=None)
    ap.add_argument("--long", type=Path, default=None, help="runs of `lengthgen long`")
    ap.add_argument("--out", type=Path, default=Path("results/a2"))
    a = ap.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    runs = load_runs(a.dir)
    (a.out / "lengthgen.json").write_text(json.dumps(runs))
    text = ("Median over seeds of the final loss divided by the loss of the history-free predictor, at "
            "positions 1-16 / 17-32 / 33-64. Training sequences have 16 symbols.\n\n" + lg_table(runs) + "\n")
    if a.long and a.long.exists():
        long = load_runs(a.long)
        (a.out / "lengthgen_long.json").write_text(json.dumps(long))
        t = long[0]["train_len"]
        text += (f"\nTraining sequences of {t} symbols: positions 1-{t} / {t + 1}-{2 * t} / "
                 f"{2 * t + 1}-{4 * t}.\n\n" + lg_table(long) + "\n")
    if a.probes and a.probes.exists():
        probes = json.loads(a.probes.read_text())
        for d in sorted({r["depth"] for r in probes}):
            text += f"\nReadouts at depth {d} (medians over seeds, final weights).\n\n" + probe_table(probes, d) + "\n"
    (a.out / "a2.md").write_text(text)
    print(text)
    figure(runs, a.out)


if __name__ == "__main__":
    main()
