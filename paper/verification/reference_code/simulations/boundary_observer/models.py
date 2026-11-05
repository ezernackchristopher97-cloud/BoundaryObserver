"""Finite generative models and hidden-factor constructions.

The classes in this module are executable illustrations of definitions in
``BoundaryObserver.lean``.  They are not additional proofs: every result is a
calculation over the explicitly enumerated finite states supplied to a model.
"""

from __future__ import annotations

from dataclasses import dataclass
from math import comb
from types import MappingProxyType
from typing import Hashable, Iterable, Mapping


def _as_unique_tuple(values: Iterable[Hashable], label: str) -> tuple[Hashable, ...]:
    result = tuple(values)
    try:
        distinct_count = len(set(result))
    except TypeError as error:
        raise TypeError(f"{label} must contain only hashable values") from error
    if distinct_count != len(result):
        raise ValueError(f"{label} must not contain duplicates")
    return result


def _sort_key(value: Hashable) -> tuple[str, str]:
    return (type(value).__qualname__, repr(value))


def canonical_set_representation(values: Iterable[Hashable]) -> str:
    """Return a stable, human-readable representation of a finite set."""

    ordered = sorted(values, key=_sort_key)
    return "{" + ", ".join(repr(value) for value in ordered) + "}"


@dataclass(frozen=True)
class GenerativeModel:
    """An explicitly enumerated finite latent model.

    ``observation_space`` is the finite accessible codomain.  The reachable
    observations are its subset hit by ``observation_by_state``.
    """

    name: str
    latent_states: tuple[Hashable, ...]
    observation_space: tuple[Hashable, ...]
    observation_by_state: Mapping[Hashable, Hashable]
    hidden_factor_kind: str | None = None
    hidden_multiplicity: int = 1
    base_model_name: str | None = None

    def __post_init__(self) -> None:
        latent_states = _as_unique_tuple(self.latent_states, "latent_states")
        observation_space = _as_unique_tuple(
            self.observation_space, "observation_space"
        )
        observation_by_state = dict(self.observation_by_state)

        if set(observation_by_state) != set(latent_states):
            missing = set(latent_states) - set(observation_by_state)
            extra = set(observation_by_state) - set(latent_states)
            raise ValueError(
                "observation_by_state must map every and only latent state; "
                f"missing={missing!r}, extra={extra!r}"
            )
        outside_space = set(observation_by_state.values()) - set(observation_space)
        if outside_space:
            raise ValueError(
                "every generated observation must belong to observation_space; "
                f"outside={outside_space!r}"
            )
        if self.hidden_multiplicity < 1:
            raise ValueError("hidden_multiplicity must be at least 1")

        object.__setattr__(self, "latent_states", latent_states)
        object.__setattr__(self, "observation_space", observation_space)
        object.__setattr__(
            self, "observation_by_state", MappingProxyType(observation_by_state)
        )

    def observe(self, latent_state: Hashable) -> Hashable:
        """Apply the finite observation function to one latent state."""

        return self.observation_by_state[latent_state]

    @property
    def latent_state_count(self) -> int:
        return len(self.latent_states)

    @property
    def reachable_observations(self) -> frozenset[Hashable]:
        return frozenset(self.observation_by_state.values())

    @property
    def reachable_observation_count(self) -> int:
        return len(self.reachable_observations)

    def observation_fibers(
        self, *, include_unreachable: bool = False
    ) -> dict[Hashable, tuple[Hashable, ...]]:
        """Return the latent fiber over each reachable (or all) observation(s)."""

        observations = (
            self.observation_space
            if include_unreachable
            else tuple(
                observation
                for observation in self.observation_space
                if observation in self.reachable_observations
            )
        )
        fibers: dict[Hashable, list[Hashable]] = {
            observation: [] for observation in observations
        }
        for latent_state in self.latent_states:
            observation = self.observe(latent_state)
            if observation in fibers:
                fibers[observation].append(latent_state)
        return {
            observation: tuple(states) for observation, states in fibers.items()
        }

    @property
    def latent_collision_count(self) -> int:
        """Count unordered pairs of distinct states sharing an observation."""

        return sum(
            comb(len(fiber), 2)
            for fiber in self.observation_fibers().values()
        )

    @property
    def is_injective(self) -> bool:
        return all(
            len(fiber) <= 1 for fiber in self.observation_fibers().values()
        )

    @property
    def exact_latent_decoder_possible(self) -> bool:
        """Decide existence of a left inverse for this explicit finite map.

        For an inhabited latent space, this is equivalent to injectivity.  The
        empty-domain edge case also requires an empty observation codomain,
        because no function from a nonempty type into an empty type exists.
        """

        if not self.latent_states:
            return not self.observation_space
        return self.is_injective

    @property
    def average_fiber_size(self) -> float:
        if not self.reachable_observations:
            return 0.0
        return self.latent_state_count / self.reachable_observation_count

    @property
    def maximum_fiber_size(self) -> int:
        fibers = self.observation_fibers().values()
        return max((len(fiber) for fiber in fibers), default=0)

    @property
    def has_boolean_hidden_factor(self) -> bool:
        return self.hidden_factor_kind == "boolean"

    def is_empirically_equivalent_to(self, other: GenerativeModel) -> bool:
        """Compare models by equality of their reachable observation sets."""

        return self.reachable_observations == other.reachable_observations

    def summary(self) -> dict[str, object]:
        return {
            "model": self.name,
            "latent_state_count": self.latent_state_count,
            "reachable_observation_count": self.reachable_observation_count,
            "reachable_observations": canonical_set_representation(
                self.reachable_observations
            ),
            "average_fiber_size": self.average_fiber_size,
            "maximum_fiber_size": self.maximum_fiber_size,
            "latent_collision_count": self.latent_collision_count,
            "observation_function_injective": self.is_injective,
            "exact_latent_decoder_possible": self.exact_latent_decoder_possible,
            "hidden_factor_kind": self.hidden_factor_kind or "none",
            "hidden_multiplicity": self.hidden_multiplicity,
        }


def make_base_model(
    latent_state_count: int,
    *,
    injective: bool,
    observation_count: int | None = None,
    name: str | None = None,
) -> GenerativeModel:
    """Create a configurable base model on states ``0, ..., n - 1``."""

    if latent_state_count < 1:
        raise ValueError("latent_state_count must be at least 1")
    latent_states = tuple(range(latent_state_count))

    if injective:
        if observation_count not in (None, latent_state_count):
            raise ValueError(
                "an injective base model uses one observation per latent state"
            )
        observation_count = latent_state_count
        observation_by_state = {state: state for state in latent_states}
        default_name = f"injective_base_{latent_state_count}"
    else:
        if latent_state_count < 2:
            raise ValueError("a noninjective base model needs at least two states")
        if observation_count is None:
            observation_count = max(1, latent_state_count // 2)
        if not 1 <= observation_count < latent_state_count:
            raise ValueError(
                "a noninjective base model needs 1 <= observation_count < "
                "latent_state_count"
            )
        observation_by_state = {
            state: state % observation_count for state in latent_states
        }
        default_name = (
            f"noninjective_base_{latent_state_count}_to_{observation_count}"
        )

    return GenerativeModel(
        name=name or default_name,
        latent_states=latent_states,
        observation_space=tuple(range(observation_count)),
        observation_by_state=observation_by_state,
    )


def boolean_hidden_extension(
    base: GenerativeModel, *, name: str | None = None
) -> GenerativeModel:
    """Attach a Boolean coordinate and ignore it during observation."""

    latent_states = tuple(
        (state, hidden)
        for state in base.latent_states
        for hidden in (False, True)
    )
    return GenerativeModel(
        name=name or f"{base.name}_boolean_extension",
        latent_states=latent_states,
        observation_space=base.observation_space,
        observation_by_state={
            state: base.observe(state[0]) for state in latent_states
        },
        hidden_factor_kind="boolean",
        hidden_multiplicity=2,
        base_model_name=base.name,
    )


def finite_hidden_extension(
    base: GenerativeModel,
    multiplicity: int,
    *,
    name: str | None = None,
) -> GenerativeModel:
    """Attach ``multiplicity`` hidden copies to every base latent state."""

    if multiplicity < 1:
        raise ValueError("multiplicity must be at least 1")
    latent_states = tuple(
        (state, hidden)
        for state in base.latent_states
        for hidden in range(multiplicity)
    )
    return GenerativeModel(
        name=name or f"{base.name}_{multiplicity}_fold_extension",
        latent_states=latent_states,
        observation_space=base.observation_space,
        observation_by_state={
            state: base.observe(state[0]) for state in latent_states
        },
        hidden_factor_kind="finite",
        hidden_multiplicity=multiplicity,
        base_model_name=base.name,
    )


@dataclass(frozen=True)
class EmpiricalEquivalenceClass:
    """One quotient class determined by a reachable observation set."""

    reachable_observations: frozenset[Hashable]
    models: tuple[GenerativeModel, ...]

    @property
    def canonical_representation(self) -> str:
        return canonical_set_representation(self.reachable_observations)


def group_by_empirical_equivalence(
    models: Iterable[GenerativeModel],
) -> tuple[EmpiricalEquivalenceClass, ...]:
    """Form the finite empirical quotient by reachable-set equality."""

    grouped: dict[frozenset[Hashable], list[GenerativeModel]] = {}
    for model in models:
        grouped.setdefault(model.reachable_observations, []).append(model)
    classes = [
        EmpiricalEquivalenceClass(reachable, tuple(members))
        for reachable, members in grouped.items()
    ]
    return tuple(
        sorted(classes, key=lambda item: item.canonical_representation)
    )

