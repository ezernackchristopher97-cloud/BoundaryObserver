"""Regression witnesses for the assumptions in Appendix J.

These exact finite checks supplement the manuscript derivations. They are not
Lean proofs, statistical experiments, or biological measurements.
"""
from fractions import Fraction
from itertools import product
from simulations.boundary_observer.models import GenerativeModel, boolean_hidden_extension


def test_later_collision_must_be_reachable_from_the_source():
    f = {0: 0, 1: 1}
    g = {0: 0, 1: 1, 2: 1}
    assert g[1] == g[2]
    assert {x: g[f[x]] for x in f} == f
    # If the original states collide, all deterministic downstream maps retain it.
    collapsed = {0: 1, 1: 1}
    for outputs in product(range(3), repeat=3):
        assert outputs[collapsed[0]] == outputs[collapsed[1]]


def test_nondecodable_base_and_extension_have_the_same_decoder_status():
    base = GenerativeModel('constant', (0, 1), (0,), {0: 0, 1: 0})
    extended = boolean_hidden_extension(base)
    assert base.is_empirically_equivalent_to(extended)
    assert not base.exact_latent_decoder_possible
    assert not extended.exact_latent_decoder_possible


def test_empty_domain_and_empty_codomain_are_distinct_decoder_cases():
    empty = GenerativeModel('empty', (), (), {})
    unreachable = GenerativeModel('unreachable', (), (0,), {})
    assert empty.is_injective and empty.exact_latent_decoder_possible
    assert unreachable.is_injective and not unreachable.exact_latent_decoder_possible


def test_equal_reachable_sets_do_not_imply_equal_probability_laws():
    low = {0: Fraction(9, 10), 1: Fraction(1, 10)}
    high = {0: Fraction(1, 10), 1: Fraction(9, 10)}
    assert sum(low.values()) == sum(high.values()) == 1
    assert {x for x, p in low.items() if p > 0} == {x for x, p in high.items() if p > 0}
    assert low[1] != high[1]


def test_two_temporal_outputs_reconstruct_state_with_the_stated_error_bound():
    for a, b in product(range(-3, 4), repeat=2):
        for T in (Fraction(-2), Fraction(1, 100), Fraction(1, 2), Fraction(2)):
            y0, yT = Fraction(a), a + T*b
            assert (y0, (yT-y0)/T) == (a, b)
            eta = Fraction(1, 1000)
            for e0, eT in product((-eta, Fraction(0), eta), repeat=2):
                recovered = ((yT+eT)-(y0+e0))/T
                assert abs(recovered-b) <= 2*eta/abs(T)
            assert abs(((yT+eta)-(y0-eta))/T-b) == 2*eta/abs(T)


def test_decoder_decision_matches_exhaustive_search_over_all_small_maps():
    # Independently enumerate total decoders, including all empty-set cases.
    for nx, no in product(range(4), repeat=2):
        X, O = tuple(range(nx)), tuple(range(no))
        for observation in product(O, repeat=nx):
            model = GenerativeModel('enumerated', X, O, dict(zip(X, observation)))
            exists = any(all(decoder[observation[x]] == x for x in X)
                         for decoder in product(X, repeat=no))
            assert model.exact_latent_decoder_possible == exists
