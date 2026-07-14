"""Tabular analyses for the finite BoundaryObserver simulations."""

from __future__ import annotations

from typing import Iterable

from .experiments import (
    AdmissibleExperiment,
    ObservationPredicate,
    predicate_profile,
)
from .models import (
    GenerativeModel,
    canonical_set_representation,
    finite_hidden_extension,
    group_by_empirical_equivalence,
)
from .interfaces import (
    FiniteObserverInterface,
    InterfaceRefinement,
    find_refinement,
)


def interface_summary_rows(
    interfaces: Iterable[FiniteObserverInterface],
) -> list[dict[str, object]]:
    return [interface.summary() for interface in interfaces]


def refinement_summary_rows(
    refinements: Iterable[InterfaceRefinement],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for refinement in refinements:
        reverse = find_refinement(refinement.coarse, refinement.fine)
        rows.append(
            {
                "refinement": refinement.name,
                "fine_interface": refinement.fine.name,
                "coarse_interface": refinement.coarse.name,
                "observation_preserved": refinement.observation_preserved,
                "fine_obs_equivalence_implies_coarse": (
                    refinement.preserves_observational_equivalence
                ),
                "strict_refinement": refinement.is_strict,
                "collapsed_world_pair_count": len(refinement.collapsed_pairs()),
                "reverse_refinement_exists": reverse is not None,
                "same_observational_resolution": (
                    refinement.same_observational_resolution
                ),
                "fine_quotient_size": refinement.fine.observable_quotient_size,
                "coarse_quotient_size": (
                    refinement.coarse.observable_quotient_size
                ),
                "quotient_map_surjective": refinement.quotient_map_surjective,
                "quotient_map_injective": refinement.quotient_map_injective,
                "quotient_map_bijective": refinement.quotient_map_bijective,
            }
        )
    return rows


def quotient_map_rows(
    refinements: Iterable[InterfaceRefinement],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for refinement in refinements:
        for fine_class, coarse_class in refinement.quotient_map_entries():
            rows.append(
                {
                    "refinement": refinement.name,
                    "fine_observation": repr(fine_class.observation),
                    "fine_class_members": fine_class.canonical_members,
                    "coarse_observation": repr(coarse_class.observation),
                    "coarse_class_members": coarse_class.canonical_members,
                }
            )
    return rows


def collapsed_pair_rows(
    refinements: Iterable[InterfaceRefinement],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for refinement in refinements:
        for left, right in refinement.collapsed_pairs():
            rows.append(
                {
                    "refinement": refinement.name,
                    "left_world_state": repr(left),
                    "right_world_state": repr(right),
                    "left_fine_observation": repr(refinement.fine.observe(left)),
                    "right_fine_observation": repr(refinement.fine.observe(right)),
                    "common_coarse_observation": repr(
                        refinement.coarse.observe(left)
                    ),
                }
            )
    return rows


def observation_fiber_rows(
    models: Iterable[GenerativeModel],
) -> list[dict[str, object]]:
    """Enumerate every finite fiber, including empty codomain fibers."""

    rows: list[dict[str, object]] = []
    for model in models:
        for observation, fiber in model.observation_fibers(
            include_unreachable=True
        ).items():
            rows.append(
                {
                    "model": model.name,
                    "observation": repr(observation),
                    "reachable": bool(fiber),
                    "fiber_size": len(fiber),
                    "latent_states_in_fiber": "; ".join(
                        repr(state) for state in fiber
                    ),
                }
            )
    return rows


def summarize_multiplicities(
    base: GenerativeModel, multiplicities: Iterable[int]
) -> tuple[list[dict[str, object]], list[GenerativeModel]]:
    rows: list[dict[str, object]] = []
    models: list[GenerativeModel] = []
    for multiplicity in multiplicities:
        model = finite_hidden_extension(base, multiplicity)
        models.append(model)
        row = model.summary()
        row["empirically_equivalent_to_base"] = (
            model.is_empirically_equivalent_to(base)
        )
        rows.append(row)
    return rows, models


def compare_experiment_outcomes(
    base: GenerativeModel,
    models: Iterable[GenerativeModel],
    experiments: Iterable[AdmissibleExperiment],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for experiment in experiments:
        base_outcomes = experiment.possible_outcomes(base)
        for model in models:
            outcomes = experiment.possible_outcomes(model)
            rows.append(
                {
                    "experiment": experiment.name,
                    "model": model.name,
                    "hidden_multiplicity": model.hidden_multiplicity,
                    "possible_outcomes": canonical_set_representation(outcomes),
                    "outcome_count": len(outcomes),
                    "matches_base_outcomes": outcomes == base_outcomes,
                }
            )
    return rows


def predicate_profile_rows(
    base: GenerativeModel,
    models: Iterable[GenerativeModel],
    predicates: Iterable[ObservationPredicate],
) -> list[dict[str, object]]:
    predicates = tuple(predicates)
    base_profile = predicate_profile(base, predicates)
    rows: list[dict[str, object]] = []
    for model in models:
        model_profile = predicate_profile(model, predicates)
        for predicate in predicates:
            entries = model_profile[predicate.name]
            formatted = "; ".join(
                f"{observation!r}:{value}"
                for observation, value in sorted(
                    entries, key=lambda item: (type(item[0]).__qualname__, repr(item[0]))
                )
            )
            rows.append(
                {
                    "model": model.name,
                    "predicate": predicate.name,
                    "profile": formatted,
                    "matches_base_profile": (
                        entries == base_profile[predicate.name]
                    ),
                }
            )
    return rows


def empirical_quotient_rows(
    models: Iterable[GenerativeModel],
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for class_index, equivalence_class in enumerate(
        group_by_empirical_equivalence(models), start=1
    ):
        cardinalities = sorted(
            {model.latent_state_count for model in equivalence_class.models}
        )
        rows.append(
            {
                "empirical_class": class_index,
                "canonical_reachable_observations": (
                    equivalence_class.canonical_representation
                ),
                "model_names": "; ".join(
                    model.name for model in equivalence_class.models
                ),
                "latent_cardinalities": "; ".join(
                    str(cardinality) for cardinality in cardinalities
                ),
                "contains_multiple_latent_cardinalities": len(cardinalities) > 1,
            }
        )
    return rows


def nonidentifiable_property_rows(
    base: GenerativeModel,
    extension: GenerativeModel,
    experiments: Iterable[AdmissibleExperiment],
) -> list[dict[str, object]]:
    """Compare latent properties inside one tested empirical class."""

    experiments = tuple(experiments)
    same_reachable = base.is_empirically_equivalent_to(extension)
    same_experiment_outcomes = all(
        experiment.possible_outcomes(base)
        == experiment.possible_outcomes(extension)
        for experiment in experiments
    )
    properties = {
        "latent cardinality": (
            base.latent_state_count,
            extension.latent_state_count,
        ),
        "maximum observation fiber size": (
            base.maximum_fiber_size,
            extension.maximum_fiber_size,
        ),
        "existence of an exact latent decoder": (
            base.exact_latent_decoder_possible,
            extension.exact_latent_decoder_possible,
        ),
        "presence of a Boolean hidden factor": (
            base.has_boolean_hidden_factor,
            extension.has_boolean_hidden_factor,
        ),
    }
    return [
        {
            "property": property_name,
            "base_value": base_value,
            "extension_value": extension_value,
            "varies_within_empirical_class": base_value != extension_value,
            "reachable_observations_equal": same_reachable,
            "all_tested_experiment_outcomes_equal": same_experiment_outcomes,
        }
        for property_name, (base_value, extension_value) in properties.items()
    ]
