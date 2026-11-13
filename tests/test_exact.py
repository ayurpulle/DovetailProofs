from fractions import Fraction as Fr
from itertools import product

from predictive import monoid
from predictive.dataset import enumerate_contexts
from predictive.ghmm import block_fooling_bound, hmm_dimension_lower_bound
from predictive.processes import REGISTRY, get, mod_counter, rrxor, square_chain, twisted_square, z1r


def test_probabilities_are_consistent():
    for name in REGISTRY:
        g = get(name)
        for n in range(4):
            assert sum(g.prob(w) for w in product(range(g.k), repeat=n)) == 1


def test_paper_counts():
    # |X_p| and |S_p| as reported in the paper for Z1R and RRXOR
    for g, n_states, n_monoid in ((z1r(), 7, 14), (rrxor(), 36, 73)):
        pm = g.predictive_machine()
        assert pm.complete and len(pm) == n_states
        assert monoid.summarise(pm).size == n_monoid


def test_algebraic_class():
    assert monoid.summarise(z1r().predictive_machine()).aperiodic
    assert not monoid.summarise(rrxor().predictive_machine()).aperiodic
    assert monoid.summarise(mod_counter(5).predictive_machine()).max_period == 5


def test_square_chain_has_d_below_n():
    g = square_chain()
    assert g.hankel_rank == 3
    assert hmm_dimension_lower_bound(g) == 4  # so n >= 4
    assert g.is_hmm and g.n == 4  # and n <= 4
    assert g.predictive_machine().complete  # finite belief set


def test_conditionals_match_brute_force():
    g = rrxor()
    cs = enumerate_contexts(g, 6)
    assert sum(cs.probs) == 1
    for w, t, p in zip(cs.contexts, cs.targets, cs.probs):
        assert g.prob(w) == p
        assert t == tuple(g.prob(w + (o,)) / p for o in range(g.k))


def test_same_state_means_same_futures():
    g = rrxor()
    cs = enumerate_contexts(g, 5)
    futures = list(product(range(2), repeat=4))
    law = lambda w: tuple(g.prob(w + v) / g.prob(w) for v in futures)
    by_state = {}
    for w, s in zip(cs.contexts, cs.state_ids):
        assert by_state.setdefault(s, law(w)) == law(w)


def test_split_is_a_partition():
    cs = enumerate_contexts(mod_counter(3), 4)
    tr, he = cs.split(0.3, seed=1)
    assert sorted(tr + he) == list(range(len(cs))) and not set(tr) & set(he)
    assert abs(len(tr) - 0.3 * len(cs)) <= 1
    assert all(sum(t) == Fr(1) for t in cs.targets)


FOOLING_CELLS = [(0, 0), (1, 2), (2, 1), (3, 3)]


def test_twisted_square_has_d_below_n_and_is_not_local():
    g = twisted_square(3)
    assert g.hankel_rank == 9
    assert block_fooling_bound(g, 4, 3, FOOLING_CELLS) == 12  # n >= 12
    assert g.is_hmm and g.n == 12  # n <= 12
    assert g.predictive_machine().complete
    cs = enumerate_contexts(g, 8)
    # no suffix of length 4 determines the next-symbol law
    by_suffix = {}
    for w, t in zip(cs.contexts, cs.targets):
        by_suffix.setdefault(w[-4:], set()).add(t)
    assert all(len(v) > 1 for v in by_suffix.values())
    # the law is a function of the last symbol and the sum of the context mod 3
    by_key = {}
    for w, t in zip(cs.contexts, cs.targets):
        assert by_key.setdefault((w[-1], sum(w) % 3), t) == t


def test_generic_square_is_a_matched_control():
    tw, gen = twisted_square(3), twisted_square(3, generic=True)
    assert gen.hankel_rank == 12 and gen.n == 12
    assert block_fooling_bound(gen, 4, 3, FOOLING_CELLS) == 12
    a, b = enumerate_contexts(tw, 8), enumerate_contexts(gen, 8)
    assert a.contexts == b.contexts
    assert a.n_distinct_targets == b.n_distinct_targets == 12
