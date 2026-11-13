"""Context-enumeration datasets for interpolation experiments.

Every possible context of a fixed length L is listed with its exact
next-symbol law.  A model is trained on a fraction of the contexts with a loss
at the final position only, and tested on the rest.
"""

from __future__ import annotations

import random
from dataclasses import dataclass
from fractions import Fraction as Fr

from .ghmm import GHMM
from .linalg import dot, vecmat


@dataclass(frozen=True)
class ContextSet:
    process: str
    length: int
    alphabet: int
    contexts: tuple  # words, as tuples of symbols
    targets: tuple  # next-symbol laws, as tuples of Fractions
    probs: tuple  # p(context)
    state_ids: tuple  # index of the predictive state reached, local to this set

    def __len__(self) -> int:
        return len(self.contexts)

    @property
    def n_states(self) -> int:
        """Distinct predictive states reached at this length."""
        return len(set(self.state_ids))

    @property
    def n_distinct_targets(self) -> int:
        """Distinct next-symbol laws: the cost of memorising, in classes."""
        return len(set(self.targets))

    def split(self, frac: float, seed: int) -> tuple[list[int], list[int]]:
        """Indices of a random train / held-out split with train fraction `frac`."""
        idx = list(range(len(self)))
        random.Random(seed).shuffle(idx)
        n_train = max(1, min(len(idx) - 1, round(frac * len(idx))))
        return sorted(idx[:n_train]), sorted(idx[n_train:])


def enumerate_contexts(g: GHMM, length: int, max_contexts: int = 2_000_000) -> ContextSet:
    """All words of the given length with positive probability, depth first.

    Walks the canonical predictive machine when it is finite, which is fast,
    and falls back to exact forward vectors otherwise.
    """
    pm = g.predictive_machine()
    contexts, targets, probs, keys = [], [], [], []

    def emit(word, target, p, key):
        if len(contexts) >= max_contexts:
            raise ValueError("too many contexts; lower the length")
        contexts.append(word)
        targets.append(target)
        probs.append(p)
        keys.append(key)

    if pm.complete:
        stack = [((), 0, Fr(1))]
        while stack:
            word, s, p = stack.pop()
            if len(word) == length:
                emit(word, pm.cond[s], p, s)
                continue
            for o in reversed(range(g.k)):
                nxt = pm.step[s][o]
                if nxt is not None:
                    stack.append((word + (o,), nxt, p * pm.cond[s][o]))
    else:
        ids: dict = {}

        def walk(word: tuple, eta: tuple, p: Fr) -> None:
            # eta is kept normalised so the fractions stay small
            if len(word) == length:
                emit(word, g.conditional(eta), p, ids.setdefault(g.state_key(eta), len(ids)))
                return
            for o, t in enumerate(g.T):
                nxt = vecmat(eta, t)
                z = dot(nxt, g.final)
                if z:
                    walk(word + (o,), tuple(x / z for x in nxt), p * z)

        walk((), g.init, Fr(1))
    return ContextSet(
        g.name, length, g.k, tuple(contexts), tuple(targets), tuple(probs), tuple(keys)
    )
