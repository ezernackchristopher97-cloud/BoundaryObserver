"""Tests for experiments, predicates, and the finite empirical quotient."""

from simulations.boundary_observer.experiments import (
    ObservationPredicate,
    categorical_partition_experiment,
    compressed_numerical_experiment,
    identity_experiment,
    predicate_success_profile,
    predicate_truth_profile,
    threshold_experiment,
)
from simulations.boundary_observer.models import (
    boolean_hidden_extension,
    finite_hidden_extension,
    group_by_empirical_equivalence,
    make_base_model,
)


def example_experiments():
    return (
        identity_experiment(),
        threshold_experiment(3),
        categorical_partition_experiment(
            {"low": (0, 1), "middle": (2, 3), "high": (4, 5)}
        ),
        compressed_numerical_experiment(2),
    )


def test_observationally_equivalent_models_have_equal_outcome_sets() -> None:
    base = make_base_model(6, injective=True)
    extensions = (
        boolean_hidden_extension(base),
        finite_hidden_extension(base, 3),
        finite_hidden_extension(base, 7),
    )

    for experiment in example_experiments():
        expected = experiment.possible_outcomes(base)
        assert all(
            experiment.possible_outcomes(extension) == expected
            for extension in extensions
        )


def test_predicate_success_profiles_agree_for_equivalent_models() -> None:
    base = make_base_model(6, injective=True)
    extension = finite_hidden_extension(base, 5)
    predicates = (
        ObservationPredicate("even", lambda observation: observation % 2 == 0),
        ObservationPredicate("at_least_three", lambda observation: observation >= 3),
    )

    assert predicate_success_profile(base, predicates) == predicate_success_profile(
        extension, predicates
    )


def test_predicate_truth_profiles_agree_for_equivalent_models() -> None:
    base = make_base_model(6, injective=True)
    extension = finite_hidden_extension(base, 5)
    predicates = (
        ObservationPredicate("even", lambda observation: observation % 2 == 0),
        ObservationPredicate("at_least_three", lambda observation: observation >= 3),
    )

    assert predicate_truth_profile(base, predicates) == predicate_truth_profile(
        extension, predicates
    )


def test_empirical_quotient_grouping_is_determined_by_reachable_sets() -> None:
    injective = make_base_model(6, injective=True, name="injective")
    same_observations_more_latents = finite_hidden_extension(
        injective, 4, name="four_fold"
    )
    same_observations_boolean = boolean_hidden_extension(
        injective, name="boolean"
    )
    different_observations = make_base_model(
        6,
        injective=False,
        observation_count=3,
        name="noninjective",
    )

    classes = group_by_empirical_equivalence(
        (
            injective,
            same_observations_more_latents,
            same_observations_boolean,
            different_observations,
        )
    )

    assert len(classes) == 2
    injective_class = next(
        empirical_class
        for empirical_class in classes
        if injective.reachable_observations
        == empirical_class.reachable_observations
    )
    assert {model.name for model in injective_class.models} == {
        "injective",
        "four_fold",
        "boolean",
    }
    assert {model.latent_state_count for model in injective_class.models} == {
        6,
        12,
        24,
    }
