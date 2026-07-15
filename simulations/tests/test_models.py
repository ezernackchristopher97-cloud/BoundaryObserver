"""Tests for finite models and hidden extensions."""

from simulations.boundary_observer.models import (
    boolean_hidden_extension,
    finite_hidden_extension,
    make_base_model,
)


def test_base_examples_include_injective_and_noninjective_maps() -> None:
    injective = make_base_model(6, injective=True)
    noninjective = make_base_model(6, injective=False, observation_count=3)

    assert injective.is_injective
    assert injective.exact_latent_decoder_possible
    assert not noninjective.is_injective
    assert not noninjective.exact_latent_decoder_possible
    assert noninjective.latent_collision_count == 3


def test_boolean_extension_preserves_reachable_observations() -> None:
    base = make_base_model(5, injective=True)
    extension = boolean_hidden_extension(base)

    assert extension.reachable_observations == base.reachable_observations
    assert extension.is_empirically_equivalent_to(base)
    assert extension.latent_state_count == 2 * base.latent_state_count


def test_boolean_extension_is_noninjective_for_inhabited_base() -> None:
    base = make_base_model(4, injective=True)
    extension = boolean_hidden_extension(base)

    assert (0, False) != (0, True)
    assert extension.observe((0, False)) == extension.observe((0, True))
    assert not extension.is_injective
    assert extension.latent_collision_count > 0


def test_strict_hidden_extension_prevents_exact_decoding() -> None:
    base = make_base_model(4, injective=True)
    extension = finite_hidden_extension(base, 2)

    assert base.exact_latent_decoder_possible
    assert not extension.exact_latent_decoder_possible


def test_finite_multiplicity_extensions_preserve_empirical_equivalence() -> None:
    base = make_base_model(7, injective=False, observation_count=3)

    for multiplicity in (1, 2, 3, 5, 8):
        extension = finite_hidden_extension(base, multiplicity)
        assert extension.reachable_observations == base.reachable_observations
        assert extension.is_empirically_equivalent_to(base)
        assert extension.latent_state_count == (
            multiplicity * base.latent_state_count
        )


def test_observation_fibers_include_unreachable_observations_on_request() -> None:
    base = make_base_model(3, injective=True)
    model = type(base)(
        name="base_with_unreachable_observation",
        latent_states=base.latent_states,
        observation_space=base.observation_space + (99,),
        observation_by_state=base.observation_by_state,
    )

    assert 99 not in model.observation_fibers()
    assert model.observation_fibers(include_unreachable=True)[99] == ()
