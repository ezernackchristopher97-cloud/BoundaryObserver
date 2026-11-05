"""Finite observer interfaces, refinements, and induced quotient maps.

This module computes finite instances of the interface-refinement definitions
in ``BoundaryObserver.lean``.  The checks are exhaustive for the enumerated
worlds supplied here, but they are illustrations rather than new proofs.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from types import MappingProxyType
from typing import Hashable, Iterable, Mapping

from .models import canonical_set_representation


def _unique_tuple(values: Iterable[Hashable], label: str) -> tuple[Hashable, ...]:
    result = tuple(values)
    try:
        if len(result) != len(set(result)):
            raise ValueError(f"{label} must not contain duplicates")
    except TypeError as error:
        raise TypeError(f"{label} must contain only hashable values") from error
    return result


@dataclass(frozen=True)
class ObservableClass:
    """One finite equivalence class under equality of observations."""

    observation: Hashable
    members: tuple[Hashable, ...]

    @property
    def canonical_members(self) -> str:
        return canonical_set_representation(self.members)


@dataclass(frozen=True)
class FiniteObserverInterface:
    """An explicitly enumerated finite counterpart of ``ObserverInterface``."""

    name: str
    world_states: tuple[Hashable, ...]
    observation_space: tuple[Hashable, ...]
    observation_by_state: Mapping[Hashable, Hashable]

    def __post_init__(self) -> None:
        world_states = _unique_tuple(self.world_states, "world_states")
        observation_space = _unique_tuple(
            self.observation_space, "observation_space"
        )
        observation_by_state = dict(self.observation_by_state)
        if set(observation_by_state) != set(world_states):
            raise ValueError(
                "observation_by_state must map every and only world state"
            )
        outside = set(observation_by_state.values()) - set(observation_space)
        if outside:
            raise ValueError(
                "every produced observation must belong to observation_space; "
                f"outside={outside!r}"
            )
        object.__setattr__(self, "world_states", world_states)
        object.__setattr__(self, "observation_space", observation_space)
        object.__setattr__(
            self, "observation_by_state", MappingProxyType(observation_by_state)
        )

    def observe(self, world_state: Hashable) -> Hashable:
        return self.observation_by_state[world_state]

    def observationally_equivalent(
        self, left: Hashable, right: Hashable
    ) -> bool:
        return self.observe(left) == self.observe(right)

    @property
    def reachable_observations(self) -> frozenset[Hashable]:
        return frozenset(self.observation_by_state.values())

    def observable_classes(self) -> tuple[ObservableClass, ...]:
        return tuple(
            ObservableClass(
                observation,
                tuple(
                    state
                    for state in self.world_states
                    if self.observe(state) == observation
                ),
            )
            for observation in self.observation_space
            if observation in self.reachable_observations
        )

    @property
    def observable_quotient_size(self) -> int:
        return len(self.observable_classes())

    @property
    def is_injective(self) -> bool:
        return self.observable_quotient_size == len(self.world_states)

    def summary(self) -> dict[str, object]:
        return {
            "interface": self.name,
            "world_state_count": len(self.world_states),
            "observation_space_count": len(self.observation_space),
            "reachable_observation_count": len(self.reachable_observations),
            "reachable_observations": canonical_set_representation(
                self.reachable_observations
            ),
            "observable_quotient_size": self.observable_quotient_size,
            "observation_function_injective": self.is_injective,
        }


@dataclass(frozen=True)
class InterfaceRefinement:
    """A finite witness that ``fine`` refines ``coarse``.

    ``coarsen_by_observation`` is the explicit map from fine observations to
    coarse observations.  Construction validates the commuting equation on
    every enumerated world state.
    """

    name: str
    fine: FiniteObserverInterface
    coarse: FiniteObserverInterface
    coarsen_by_observation: Mapping[Hashable, Hashable]

    def __post_init__(self) -> None:
        if self.fine.world_states != self.coarse.world_states:
            raise ValueError("fine and coarse interfaces must share one world")
        coarsen_by_observation = dict(self.coarsen_by_observation)
        if set(coarsen_by_observation) != set(self.fine.observation_space):
            raise ValueError(
                "coarsen_by_observation must map every fine observation"
            )
        outside = set(coarsen_by_observation.values()) - set(
            self.coarse.observation_space
        )
        if outside:
            raise ValueError(
                "coarsened observations must belong to the coarse space; "
                f"outside={outside!r}"
            )
        for state in self.fine.world_states:
            if self.coarse.observe(state) != coarsen_by_observation[
                self.fine.observe(state)
            ]:
                raise ValueError(
                    "coarsening does not preserve observations at world state "
                    f"{state!r}"
                )
        object.__setattr__(
            self,
            "coarsen_by_observation",
            MappingProxyType(coarsen_by_observation),
        )

    def coarsen(self, fine_observation: Hashable) -> Hashable:
        return self.coarsen_by_observation[fine_observation]

    @property
    def observation_preserved(self) -> bool:
        return all(
            self.coarse.observe(state)
            == self.coarsen(self.fine.observe(state))
            for state in self.fine.world_states
        )

    @property
    def preserves_observational_equivalence(self) -> bool:
        return all(
            not self.fine.observationally_equivalent(left, right)
            or self.coarse.observationally_equivalent(left, right)
            for left in self.fine.world_states
            for right in self.fine.world_states
        )

    def collapsed_pairs(self) -> tuple[tuple[Hashable, Hashable], ...]:
        """Return pairs distinguished by fine and identified by coarse."""

        return tuple(
            (left, right)
            for left, right in combinations(self.fine.world_states, 2)
            if not self.fine.observationally_equivalent(left, right)
            and self.coarse.observationally_equivalent(left, right)
        )

    @property
    def is_strict(self) -> bool:
        return bool(self.collapsed_pairs())

    @property
    def same_observational_resolution(self) -> bool:
        return all(
            self.fine.observationally_equivalent(left, right)
            == self.coarse.observationally_equivalent(left, right)
            for left in self.fine.world_states
            for right in self.fine.world_states
        )

    def quotient_map_entries(
        self,
    ) -> tuple[tuple[ObservableClass, ObservableClass], ...]:
        """Compute the induced map from fine classes to coarse classes."""

        coarse_classes = {
            observable_class.observation: observable_class
            for observable_class in self.coarse.observable_classes()
        }
        return tuple(
            (
                fine_class,
                coarse_classes[self.coarsen(fine_class.observation)],
            )
            for fine_class in self.fine.observable_classes()
        )

    @property
    def quotient_map_surjective(self) -> bool:
        mapped = {
            coarse_class.observation
            for _, coarse_class in self.quotient_map_entries()
        }
        return mapped == self.coarse.reachable_observations

    @property
    def quotient_map_injective(self) -> bool:
        targets = [
            coarse_class.observation
            for _, coarse_class in self.quotient_map_entries()
        ]
        return len(targets) == len(set(targets))

    @property
    def quotient_map_bijective(self) -> bool:
        return self.quotient_map_surjective and self.quotient_map_injective

    def compose(
        self,
        after: InterfaceRefinement,
        *,
        name: str | None = None,
    ) -> InterfaceRefinement:
        """Compose ``fine → middle`` with ``middle → coarse``."""

        if self.coarse is not after.fine:
            raise ValueError("refinements can compose only at a shared interface")
        return InterfaceRefinement(
            name=name or f"{self.name}_then_{after.name}",
            fine=self.fine,
            coarse=after.coarse,
            coarsen_by_observation={
                observation: after.coarsen(self.coarsen(observation))
                for observation in self.fine.observation_space
            },
        )


def find_refinement(
    fine: FiniteObserverInterface,
    coarse: FiniteObserverInterface,
    *,
    name: str | None = None,
) -> InterfaceRefinement | None:
    """Find a finite coarsening witness when one exists."""

    if fine.world_states != coarse.world_states:
        return None
    mapping: dict[Hashable, Hashable] = {}
    for fine_observation in fine.observation_space:
        coarse_values = {
            coarse.observe(state)
            for state in fine.world_states
            if fine.observe(state) == fine_observation
        }
        if len(coarse_values) > 1:
            return None
        if coarse_values:
            mapping[fine_observation] = next(iter(coarse_values))
        elif coarse.observation_space:
            mapping[fine_observation] = coarse.observation_space[0]
        else:
            return None
    return InterfaceRefinement(
        name=name or f"{fine.name}_to_{coarse.name}",
        fine=fine,
        coarse=coarse,
        coarsen_by_observation=mapping,
    )


def standard_refinement_family() -> tuple[
    tuple[FiniteObserverInterface, ...], tuple[InterfaceRefinement, ...]
]:
    """Build one strict chain plus a mutually refining relabeling example."""

    world_states = tuple(range(8))
    identity = FiniteObserverInterface(
        name="identity_interface",
        world_states=world_states,
        observation_space=world_states,
        observation_by_state={state: state for state in world_states},
    )
    paired = FiniteObserverInterface(
        name="paired_bucket_interface",
        world_states=world_states,
        observation_space=tuple(range(4)),
        observation_by_state={state: state // 2 for state in world_states},
    )
    region = FiniteObserverInterface(
        name="binary_region_interface",
        world_states=world_states,
        observation_space=("lower", "upper"),
        observation_by_state={
            state: "lower" if state < 4 else "upper"
            for state in world_states
        },
    )
    relabeled = FiniteObserverInterface(
        name="relabeled_identity_interface",
        world_states=world_states,
        observation_space=tuple(f"state_{state}" for state in world_states),
        observation_by_state={
            state: f"state_{state}" for state in world_states
        },
    )

    identity_to_paired = InterfaceRefinement(
        name="identity_to_paired",
        fine=identity,
        coarse=paired,
        coarsen_by_observation={state: state // 2 for state in world_states},
    )
    paired_to_region = InterfaceRefinement(
        name="paired_to_region",
        fine=paired,
        coarse=region,
        coarsen_by_observation={
            bucket: "lower" if bucket < 2 else "upper"
            for bucket in paired.observation_space
        },
    )
    identity_to_region = identity_to_paired.compose(
        paired_to_region, name="identity_to_region"
    )
    identity_to_relabeled = InterfaceRefinement(
        name="identity_to_relabeled",
        fine=identity,
        coarse=relabeled,
        coarsen_by_observation={
            state: f"state_{state}" for state in world_states
        },
    )
    relabeled_to_identity = InterfaceRefinement(
        name="relabeled_to_identity",
        fine=relabeled,
        coarse=identity,
        coarsen_by_observation={
            f"state_{state}": state for state in world_states
        },
    )
    return (
        identity,
        paired,
        region,
        relabeled,
    ), (
        identity_to_paired,
        paired_to_region,
        identity_to_region,
        identity_to_relabeled,
        relabeled_to_identity,
    )

