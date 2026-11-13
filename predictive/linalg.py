"""Exact linear algebra over the rationals, on tuples of Fractions.

Small and slow on purpose: the processes here have a handful of states, and
exact arithmetic is what lets ranks and state identifications be trusted.
"""

from __future__ import annotations

from fractions import Fraction as Fr
from typing import Callable, Iterable, Sequence

Vec = tuple
Mat = tuple  # tuple of row tuples


def vec(xs: Iterable) -> Vec:
    return tuple(Fr(x) for x in xs)


def mat(rows: Iterable[Iterable]) -> Mat:
    return tuple(vec(r) for r in rows)


def dot(a: Sequence, b: Sequence) -> Fr:
    return sum((x * y for x, y in zip(a, b) if x and y), Fr(0))


def vecmat(v: Sequence, m: Mat) -> Vec:
    """Row vector times matrix."""
    cols = len(m[0])
    out = [Fr(0)] * cols
    for vi, row in zip(v, m):
        if vi:
            for j, x in enumerate(row):
                if x:
                    out[j] += vi * x
    return tuple(out)


def matvec(m: Mat, v: Sequence) -> Vec:
    """Matrix times column vector."""
    return tuple(dot(row, v) for row in m)


class EchelonBasis:
    """Incrementally built basis of a subspace of Q^n."""

    def __init__(self) -> None:
        self.rows: list[list[Fr]] = []
        self.pivots: list[int] = []

    def reduce(self, v: Sequence) -> list[Fr]:
        v = list(v)
        for row, p in zip(self.rows, self.pivots):
            c = v[p]
            if c:
                v = [a - c * b for a, b in zip(v, row)]
        return v

    def add(self, v: Sequence) -> bool:
        """Add v to the span.  Returns True if it was independent."""
        r = self.reduce(v)
        p = next((i for i, x in enumerate(r) if x), None)
        if p is None:
            return False
        inv = 1 / r[p]
        self.rows.append([x * inv for x in r])
        self.pivots.append(p)
        return True

    def __len__(self) -> int:
        return len(self.rows)


def rank(rows: Iterable[Sequence]) -> int:
    basis = EchelonBasis()
    for r in rows:
        basis.add(r)
    return len(basis)


def span_closure(
    start: Iterable[Sequence], maps: Sequence[Callable[[Vec], Vec]]
) -> list[Vec]:
    """Basis of the smallest subspace containing `start` and closed under `maps`.

    The returned vectors are images of the start vectors under words in the
    maps, not the reduced echelon rows.
    """
    basis = EchelonBasis()
    found: list[Vec] = []
    queue = [tuple(v) for v in start]
    while queue:
        v = queue.pop(0)
        if basis.add(v):
            found.append(v)
            queue.extend(f(v) for f in maps)
    return found


def solve_stationary(p: Mat) -> Vec:
    """A probability row vector pi with pi P = pi, for a stochastic matrix P.

    Assumes the stationary distribution is unique.
    """
    n = len(p)
    # Rows of the system: (P^T - I) pi = 0, with one equation replaced by sum = 1.
    a = [[p[j][i] - (1 if i == j else 0) for j in range(n)] + [Fr(0)] for i in range(n)]
    a[-1] = [Fr(1)] * n + [Fr(1)]
    for col in range(n):
        piv = next(r for r in range(col, n) if a[r][col])
        a[col], a[piv] = a[piv], a[col]
        inv = 1 / a[col][col]
        a[col] = [x * inv for x in a[col]]
        for r in range(n):
            if r != col and a[r][col]:
                c = a[r][col]
                a[r] = [x - c * y for x, y in zip(a[r], a[col])]
    return tuple(a[i][n] for i in range(n))
