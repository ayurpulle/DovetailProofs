"""For each process: is there a t such that tau(O^t) contains a nontrivial group?

    python -m predictive.equallength rrxor act_z6 act_s3 act_s4 act_a5

This is the hypothesis of Theorem thm:pred-complexity(ii) of Lattice/main.tex.
"""
import sys
from .processes import get
from . import monoid

def comp(t, g):            # first t, then g (acting on the right, as in monoid.py)
    return tuple(g[i] for i in t)

def check(name):
    pm = get(name).predictive_machine(); gens = monoid.generators(pm)
    ident = tuple(range(len(pm) + 1))
    level = frozenset([ident]); seen = {}; t = 0; hits = []
    while level not in seen:
        seen[level] = t
        for g in level:
            pw = [g]; cur = comp(g, g)
            while cur not in pw:
                pw.append(cur); cur = comp(cur, g)
            if cur == g and len(pw) > 1 and all(x in level for x in pw):   # g generates a cyclic group of order len(pw) inside the level
                hits.append((t, len(pw))); break
        level = frozenset(comp(x, g) for x in level for g in gens); t += 1
    ms = monoid.summarise(pm)
    orders = sorted({o for _, o in hits})
    print(f"{name:14s} |S_p|={ms.size:3d} aperiodic={ms.aperiodic!s:5s} max period={ms.max_period} "
          f"levels until repeat={t} (first repeat of level {seen[level]}) "
          f"group inside one level: {'t=%d, cyclic of order %d' % hits[0] if hits else 'NONE'}")
for n in sys.argv[1:]: check(n)
