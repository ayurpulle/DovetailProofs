"""Generalised hidden Markov models with exact arithmetic.

Convention: states are row vectors.  A process over the alphabet
{0, ..., k-1} is given by matrices T[o], an initial row vector `init` and a
column vector `final`, with

    p(o_1 ... o_n) = init . T[o_1] ... T[o_n] . final

For an ordinary HMM, T[o][i][j] is the probability of emitting o and moving
from hidden state i to j, `init` is a distribution, and `final` is all ones.
A GHMM allows any real entries as long as every p(w) is a probability.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Fr
from functools import cached_property
from typing import Iterable, Optional, Sequence

from .linalg import Mat, Vec, dot, mat, matvec, rank, span_closure, vec, vecmat

Word = tuple


@dataclass(frozen=True)
class PredictiveMachine:
    """The canonical predictive machine, truncated if `complete` is False.

    states[i] is the normalised coordinate vector of predictive state i, with
    state 0 the initial one.  step[i][o] is the successor state, or None when
    symbol o is impossible from state i.  cond[i][o] is the probability of o.
    """

    states: tuple
    step: tuple
    cond: tuple
    complete: bool

    def __len__(self) -> int:
        return len(self.states)


@dataclass(frozen=True)
class GHMM:
    name: str
    T: tuple
    init: Vec
    final: Vec

    def __post_init__(self) -> None:
        n = len(self.init)
        assert len(self.final) == n
        assert all(len(t) == n and all(len(r) == n for r in t) for t in self.T)
        assert dot(self.init, self.final) == 1, "p(empty word) must be 1"
        total = tuple(
            tuple(sum(t[i][j] for t in self.T) for j in range(n)) for i in range(n)
        )
        assert matvec(total, self.final) == tuple(self.final), "not consistent"

    @property
    def k(self) -> int:
        """Alphabet size."""
        return len(self.T)

    @property
    def n(self) -> int:
        """Dimension of this presentation (hidden states, for an HMM)."""
        return len(self.init)

    @property
    def is_hmm(self) -> bool:
        nonneg = all(x >= 0 for t in self.T for r in t for x in r)
        return nonneg and all(x >= 0 for x in self.init) and all(x == 1 for x in self.final)

    # ---- probabilities -------------------------------------------------

    def forward(self, word: Iterable[int], start: Optional[Vec] = None) -> Vec:
        eta = self.init if start is None else start
        for o in word:
            eta = vecmat(eta, self.T[o])
        return eta

    def prob(self, word: Iterable[int]) -> Fr:
        return dot(self.forward(word), self.final)

    # ---- linear structure ----------------------------------------------

    @cached_property
    def backward_basis(self) -> tuple:
        """Basis of span{T_w final}, the futures a state can be tested against."""
        maps = [lambda v, t=t: matvec(t, v) for t in self.T]
        return tuple(span_closure([self.final], maps))

    @cached_property
    def forward_basis(self) -> tuple:
        """Basis of span{init T_w}, the reachable states."""
        maps = [lambda v, t=t: vecmat(v, t) for t in self.T]
        return tuple(span_closure([self.init], maps))

    @cached_property
    def hankel_rank(self) -> int:
        """d: the rank of the Hankel matrix H[u, v] = p(uv)."""
        return rank([[dot(f, b) for b in self.backward_basis] for f in self.forward_basis])

    # ---- predictive states ---------------------------------------------

    def state_key(self, eta: Vec) -> Optional[tuple]:
        """Canonical name of the predictive state of an unnormalised row vector.

        Two histories get the same key exactly when they have the same
        conditional law over all futures.  None means the history is impossible.
        """
        z = dot(eta, self.final)
        if z == 0:
            return None
        return tuple(dot(eta, b) / z for b in self.backward_basis)

    def conditional(self, eta: Vec) -> tuple:
        """Next-symbol law after a possible history with forward vector eta."""
        z = dot(eta, self.final)
        return tuple(dot(vecmat(eta, t), self.final) / z for t in self.T)

    def predictive_machine(self, max_states: int = 5000) -> PredictiveMachine:
        """Breadth-first construction of the canonical predictive machine."""
        ids = {self.state_key(self.init): 0}
        reps = [self.init]
        step: list[list] = []
        cond: list[tuple] = []
        complete = True
        i = 0
        while i < len(reps):
            eta = reps[i]
            row = []
            for t in self.T:
                nxt = vecmat(eta, t)
                z = dot(nxt, self.final)
                if z == 0:
                    row.append(None)
                    continue
                nxt = tuple(x / z for x in nxt)
                key = self.state_key(nxt)
                if key not in ids:
                    if len(reps) >= max_states:
                        complete = False
                        row.append(None)
                        continue
                    ids[key] = len(reps)
                    reps.append(nxt)
                row.append(ids[key])
            step.append(row)
            cond.append(self.conditional(eta))
            i += 1
        states = tuple(self.state_key(r) for r in reps)
        return PredictiveMachine(states, tuple(map(tuple, step)), tuple(cond), complete)


def hmm_from_edges(
    name: str,
    n_states: int,
    alphabet: int,
    edges: Sequence[tuple],
    init: Optional[Sequence] = None,
) -> GHMM:
    """Build an HMM from edges (source, symbol, target, probability).

    If `init` is None the stationary distribution of the hidden chain is used.
    """
    T = [[[Fr(0)] * n_states for _ in range(n_states)] for _ in range(alphabet)]
    for i, o, j, pr in edges:
        T[o][i][j] += Fr(pr)
    Tm = tuple(mat(t) for t in T)
    if init is None:
        from .linalg import solve_stationary

        total = tuple(
            tuple(sum(t[i][j] for t in Tm) for j in range(n_states)) for i in range(n_states)
        )
        init_v = solve_stationary(total)
    else:
        init_v = vec(init)
    return GHMM(name, Tm, init_v, vec([1] * n_states))


def markov_chain(name: str, P: Sequence[Sequence], init: Optional[Sequence] = None) -> GHMM:
    """First-order Markov chain on symbols with transition matrix P.

    With `init` None the chain is stationary and the presentation has one
    hidden state per symbol (the previous symbol, drawn from the stationary
    law).  Otherwise `init` is the distribution of the first symbol and the
    presentation has one extra start state.
    """
    P = mat(P)
    k = len(P)
    step = [(i, o, o, P[i][o]) for i in range(k) for o in range(k) if P[i][o]]
    if init is None:
        from .linalg import solve_stationary

        return hmm_from_edges(name, k, k, step, init=solve_stationary(P))
    init = vec(init)
    edges = [(0, o, o + 1, init[o]) for o in range(k) if init[o]]
    edges += [(i + 1, o, j + 1, pr) for i, o, j, pr in step]
    return hmm_from_edges(name, k + 1, k, edges, init=[1] + [0] * k)


# ---- lower bounds on the minimal HMM dimension n -------------------------


def hankel_block(g: GHMM, prefixes: Sequence[Word], suffixes: Sequence[Word]) -> list[list[Fr]]:
    out = []
    for u in prefixes:
        eta = g.forward(u)
        out.append([dot(g.forward(v, start=eta), g.final) for v in suffixes])
    return out


def fooling_set_bound(m: Sequence[Sequence]) -> int:
    """Lower bound on the nonnegative rank of a nonnegative matrix.

    A fooling set is a set of positive entries (i, j) such that for any two of
    them, (i, j) and (i', j'), at least one of m[i][j'], m[i'][j] is zero.  No
    nonnegative rank-one term can cover two entries of a fooling set, so its
    size bounds the nonnegative rank from below.  Exact search, small inputs only.
    """
    cells = [(i, j) for i, row in enumerate(m) for j, x in enumerate(row) if x > 0]

    def compatible(a, b):
        return m[a[0]][b[1]] == 0 or m[b[0]][a[1]] == 0

    best = 0

    def grow(chosen, rest):
        nonlocal best
        best = max(best, len(chosen))
        if len(chosen) + len(rest) <= best:
            return
        for idx, c in enumerate(rest):
            grow(chosen + [c], [d for d in rest[idx + 1 :] if compatible(c, d)])

    grow([], cells)
    return best


def hmm_dimension_lower_bound(g: GHMM, prefix_len: int = 1, suffix_len: int = 1) -> int:
    """A lower bound on n, the least number of states of any HMM for g.

    Any n-state HMM factors every Hankel block as a product of nonnegative
    matrices with inner dimension n, so n is at least the nonnegative rank of
    the block, which is at least max(rank, fooling set size).  Computing n
    exactly is hard in general: this is a certificate, not an algorithm.
    """
    from itertools import product

    prefixes = [w for w in product(range(g.k), repeat=prefix_len)]
    suffixes = [w for w in product(range(g.k), repeat=suffix_len)]
    block = hankel_block(g, prefixes, suffixes)
    return max(rank(block), fooling_set_bound(block))


def block_fooling_bound(g: GHMM, prefix_len: int, suffix_len: int, cells) -> int:
    """A lower bound on n from several mutually fooling blocks of one Hankel block.

    `cells` is a list of pairs (s, a).  Block t has the prefixes ending in s_t
    as rows and the suffixes starting with a_t as columns.  If for every two
    blocks one of the two cross blocks is identically zero, then no nonnegative
    rank-one term below the Hankel matrix can be positive on two blocks, so the
    nonnegative rank, and hence n, is at least the sum of the blocks' ranks.
    Raises if the cross-block condition fails.
    """
    from itertools import product

    prefixes = [w for w in product(range(g.k), repeat=prefix_len) if g.prob(w) > 0]
    suffixes = list(product(range(g.k), repeat=suffix_len))
    H = hankel_block(g, prefixes, suffixes)
    rows = [[i for i, u in enumerate(prefixes) if u[-1] == s] for s, _ in cells]
    cols = [[j for j, v in enumerate(suffixes) if v[0] == a] for _, a in cells]
    zero = lambda R, C: all(H[i][j] == 0 for i in R for j in C)
    for t in range(len(cells)):
        for u in range(t + 1, len(cells)):
            if not (zero(rows[t], cols[u]) or zero(rows[u], cols[t])):
                raise ValueError(f"blocks {cells[t]} and {cells[u]} do not fool each other")
    return sum(rank([[H[i][j] for j in C] for i in R]) for R, C in zip(rows, cols))
