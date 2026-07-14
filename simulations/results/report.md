# BoundaryObserver simulation report

## Scope

These are exhaustive calculations for explicitly enumerated finite examples.
They illustrate selected structures proved in `BoundaryObserver.lean`; they are
not additional mathematical proofs and are not empirical confirmation of any
metaphysical claim.

## Base examples

- `injective_base` has 6 latent states, reachable set
  `[0, 1, 2, 3, 4, 5]`, and an injective observation map.
- `noninjective_base` has 6 latent
  states, reachable set `[0, 1, 2]`,
  and a noninjective observation map.

## Boolean hidden extension

| Check | Calculated result |
| --- | --- |
| Same reachable observations | True |
| Twice as many latent states | True |
| Contains a latent collision | True |
| Globally exact latent decoder is impossible | True |
| Same empirical equivalence class | True |

## Finite hidden multiplicities

| Multiplicity | Latent states | Reachable observations | Average fiber | Maximum fiber | Collisions | Exact decoder? |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | 6 | 6 | 1.00 | 1 | 0 | True |
| 2 | 12 | 6 | 2.00 | 2 | 6 | False |
| 3 | 18 | 6 | 3.00 | 3 | 18 | False |
| 5 | 30 | 6 | 5.00 | 5 | 60 | False |
| 8 | 48 | 6 | 8.00 | 8 | 168 | False |

In this run the reachable observation set is unchanged for every listed
multiplicity.  Fiber and collision values are calculations for these models.

## Admissible experiment outcomes

| Experiment | Base possible outcomes | All listed models match |
| --- | --- | --- |
| identity | {0, 1, 2, 3, 4, 5} | True |
| threshold_at_3 | {False, True} | True |
| categorical_partition | {'high', 'low', 'middle'} | True |
| compressed_width_2 | {0, 1, 2} | True |

Each experiment is a function of accessible observations only.

## Predicate profiles

All 21 model/predicate profile comparisons match the base:
`True`.
The full truth profiles are stored in `predicate_profiles.csv`.

## Finite empirical quotient

| Class | Canonical reachable set | Latent cardinalities | Models |
| --- | --- | --- | --- |
| 1 | {0, 1, 2, 3, 4, 5} | 6; 12; 18; 30; 48 | injective_base; boolean_hidden_extension; injective_base_1_fold_extension; injective_base_2_fold_extension; injective_base_3_fold_extension; injective_base_5_fold_extension; injective_base_8_fold_extension |
| 2 | {0, 1, 2} | 6 | noninjective_base |

Class membership above is computed solely by equality of reachable observation
sets.  The canonical class label is the sorted representation of that set.

## Latent properties not fixed by this empirical class

| Latent property | Base | Boolean extension | Varies |
| --- | --- | --- | --- |
| latent cardinality | 6 | 12 | True |
| maximum observation fiber size | 1 | 2 | True |
| existence of an exact latent decoder | True | False | True |
| presence of a Boolean hidden factor | False | True | True |

For this base/extension pair, reachable observations and all tested admissible
experiment outcome sets agree while the displayed latent properties vary.
This is a finite witness within the framework, not a claim beyond it.

## Generated plots

- `latent_state_count_vs_hidden_multiplicity.png`
- `reachable_observation_count_vs_hidden_multiplicity.png`
- `maximum_fiber_size_vs_hidden_multiplicity.png`
- `experiment_outcome_count_vs_hidden_multiplicity.png`
