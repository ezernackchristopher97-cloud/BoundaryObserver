"""Tests for finite interface refinement and induced quotient maps."""

import pytest

from simulations.boundary_observer.interfaces import (
    InterfaceRefinement,
    find_refinement,
    standard_refinement_family,
)


def test_standard_refinements_preserve_observations_and_obs_equivalence() -> None:
    _, refinements = standard_refinement_family()

    assert all(refinement.observation_preserved for refinement in refinements)
    assert all(
        refinement.preserves_observational_equivalence
        for refinement in refinements
    )


def test_strict_refinements_exhibit_collapsed_pairs() -> None:
    _, refinements = standard_refinement_family()
    by_name = {refinement.name: refinement for refinement in refinements}

    assert len(by_name["identity_to_paired"].collapsed_pairs()) == 4
    assert len(by_name["paired_to_region"].collapsed_pairs()) == 8
    assert len(by_name["identity_to_region"].collapsed_pairs()) == 12
    assert by_name["identity_to_paired"].is_strict
    assert by_name["paired_to_region"].is_strict
    assert by_name["identity_to_region"].is_strict


def test_every_refinement_quotient_map_is_surjective() -> None:
    _, refinements = standard_refinement_family()

    assert all(refinement.quotient_map_surjective for refinement in refinements)


def test_strict_refinement_quotient_maps_are_not_injective() -> None:
    _, refinements = standard_refinement_family()

    for refinement in refinements:
        if refinement.is_strict:
            assert not refinement.quotient_map_injective
            assert not refinement.quotient_map_bijective


def test_strict_refinement_cannot_be_reversed() -> None:
    _, refinements = standard_refinement_family()

    for refinement in refinements:
        if refinement.is_strict:
            assert find_refinement(refinement.coarse, refinement.fine) is None


def test_mutually_refining_relabeling_has_bijective_quotient_maps() -> None:
    _, refinements = standard_refinement_family()
    by_name = {refinement.name: refinement for refinement in refinements}

    forward = by_name["identity_to_relabeled"]
    reverse = by_name["relabeled_to_identity"]
    assert forward.same_observational_resolution
    assert reverse.same_observational_resolution
    assert forward.quotient_map_bijective
    assert reverse.quotient_map_bijective


def test_composed_refinement_matches_direct_state_observations() -> None:
    _, refinements = standard_refinement_family()
    by_name = {refinement.name: refinement for refinement in refinements}
    composed = by_name["identity_to_region"]

    for state in composed.fine.world_states:
        assert composed.coarsen(composed.fine.observe(state)) == (
            composed.coarse.observe(state)
        )


def test_invalid_coarsening_witness_is_rejected() -> None:
    interfaces, _ = standard_refinement_family()
    identity, paired, _, _ = interfaces
    invalid_mapping = {state: 0 for state in identity.observation_space}

    with pytest.raises(ValueError, match="does not preserve observations"):
        InterfaceRefinement(
            name="invalid",
            fine=identity,
            coarse=paired,
            coarsen_by_observation=invalid_mapping,
        )

