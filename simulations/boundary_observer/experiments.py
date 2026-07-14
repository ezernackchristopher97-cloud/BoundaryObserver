"""Admissible observation-only experiments and finite predicate profiles."""

from __future__ import annotations

from dataclasses import dataclass
from math import floor
from typing import Callable, Hashable, Iterable, Mapping

from .models import GenerativeModel


@dataclass(frozen=True)
class AdmissibleExperiment:
    """A named function whose input is only an accessible observation."""

    name: str
    transform: Callable[[Hashable], Hashable]

    def __call__(self, observation: Hashable) -> Hashable:
        return self.transform(observation)

    def possible_outcomes(self, model: GenerativeModel) -> frozenset[Hashable]:
        return frozenset(
            self.transform(observation)
            for observation in model.reachable_observations
        )


def identity_experiment() -> AdmissibleExperiment:
    return AdmissibleExperiment("identity", lambda observation: observation)


def threshold_experiment(threshold: float) -> AdmissibleExperiment:
    return AdmissibleExperiment(
        f"threshold_at_{threshold:g}",
        lambda observation: float(observation) >= threshold,
    )


def categorical_partition_experiment(
    categories: Mapping[str, Iterable[Hashable]],
    *,
    default: str = "other",
) -> AdmissibleExperiment:
    """Partition selected observations into named accessible categories."""

    normalized = {name: frozenset(values) for name, values in categories.items()}
    assigned: set[Hashable] = set()
    for category, values in normalized.items():
        overlap = assigned.intersection(values)
        if overlap:
            raise ValueError(
                f"categorical partitions must be disjoint; {category!r} "
                f"overlaps on {overlap!r}"
            )
        assigned.update(values)

    def classify(observation: Hashable) -> str:
        for category, values in normalized.items():
            if observation in values:
                return category
        return default

    return AdmissibleExperiment("categorical_partition", classify)


def compressed_numerical_experiment(bin_width: float) -> AdmissibleExperiment:
    """Compress a numeric observation to the index of its fixed-width bin."""

    if bin_width <= 0:
        raise ValueError("bin_width must be positive")
    return AdmissibleExperiment(
        f"compressed_width_{bin_width:g}",
        lambda observation: floor(float(observation) / bin_width),
    )


@dataclass(frozen=True)
class ObservationPredicate:
    """A Boolean predicate defined solely on accessible observations."""

    name: str
    evaluate: Callable[[Hashable], bool]

    def __call__(self, observation: Hashable) -> bool:
        return bool(self.evaluate(observation))


PredicateProfile = dict[str, frozenset[tuple[Hashable, bool]]]


def predicate_profile(
    model: GenerativeModel,
    predicates: Iterable[ObservationPredicate],
) -> PredicateProfile:
    """Record every tested predicate value on every reachable observation."""

    return {
        predicate.name: frozenset(
            (observation, predicate(observation))
            for observation in model.reachable_observations
        )
        for predicate in predicates
    }
