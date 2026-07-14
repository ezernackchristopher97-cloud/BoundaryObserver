# BoundaryObserver executable simulations

This directory contains finite, inspectable Python calculations illustrating
selected structures from [`BoundaryObserver.lean`](../BoundaryObserver.lean).
The Lean development is the source of the formal theorems. These simulations
are computational demonstrations for particular enumerated models; they are
not new proofs and are not empirical confirmation of any metaphysical claim.

## Contents

- `boundary_observer/models.py` defines finite latent and observation spaces,
  an observation function, reachable observations, observation fibers,
  collisions, injectivity, and finite exact-decoder existence. It also builds
  Boolean and arbitrary finite hidden-factor extensions.
- `boundary_observer/experiments.py` defines observation-only admissible
  experiments and finite observation-predicate profiles.
- `boundary_observer/interfaces.py` defines finite observer interfaces,
  explicit refinement witnesses, strict-refinement checks, composition, and
  induced maps between observable quotient classes.
- `boundary_observer/analysis.py` compares multiplicities, outcome sets,
  predicate profiles, empirical quotient classes, interface refinements, and
  selected latent properties.
- `run_simulations.py` runs all examples and writes CSV, Markdown, and PNG
  outputs to `results/`.
- `tests/` verifies the computational analogues requested for these examples.

## Correspondence with the Lean formalization

| Python construction | Lean definition or result |
| --- | --- |
| `GenerativeModel` | `BoundaryObserver.GenerativeModel` |
| `reachable_observations` | finite enumeration of `Produces` |
| `is_empirically_equivalent_to` | finite decision procedure for `ModelObsEq` |
| `AdmissibleExperiment` | `AdmissibleExperiment` |
| `possible_outcomes` | finite enumeration of `ExperimentOutcomeSet` |
| `boolean_hidden_extension` | `duplicateModel`, equivalently `hiddenExtensionModel M Bool` |
| `finite_hidden_extension(base, m)` | hidden extension by a finite type with exactly `m` values |
| `observation_fibers` | finite enumeration of `LatentFiber` |
| empirical quotient grouping | grouping by the equality used in `ModelObsEq` |
| `FiniteObserverInterface` | `ObserverInterface` on an enumerated finite world |
| `InterfaceRefinement` | an explicit witness for `InterfaceRefines` |
| `is_strict` | finite witness search for `StrictlyRefines` |
| `quotient_map_entries` | finite enumeration of `quotientMapOfRefinement` |

The Python multiplicity argument is the literal number of hidden copies. In
Lean, `finiteMultiplicityModel M n` uses `Fin (n + 1)`, so Python multiplicity
`m` corresponds to the Lean parameter `n = m - 1`.

The Lean file formally proves general statements including:

- noninjectivity prevents a globally exact decoder;
- observationally equivalent models have the same possible outcomes for every
  admissible experiment;
- Boolean and inhabited hidden-factor extensions preserve reachable
  observations while introducing latent collisions;
- finite hidden multiplicities preserve observational equivalence and can make
  latent fibers arbitrarily large.
- refinement preserves observational equivalence and induces a surjective map
  from the finer observable quotient to the coarser quotient;
- strict refinement makes that quotient map noninjective and prevents reverse
  refinement, while mutual refinement induces a quotient equivalence.

The Python suite merely calculates these relationships for its finite sample
models. A passing Python test does not replace or strengthen a Lean theorem.

## Models and measurements

The runner includes an injective six-state base model and a noninjective
six-state/three-observation model. For every finite model it records:

- latent state count and reachable observation set;
- every reachable observation fiber;
- unordered latent collision pairs (the sum of `choose(fiber size, 2)`);
- injectivity and existence of a globally exact finite latent decoder;
- average and maximum reachable-fiber sizes.

The Boolean extension uses pairs `(base_state, hidden_boolean)` and its
observation function discards the Boolean coordinate. Finite multiplicity
extensions similarly use `(base_state, hidden_index)`.

The admissible experiments are identity, Boolean threshold, categorical
partition, and compressed numerical binning. Each receives only an accessible
observation. Predicate profiles likewise evaluate only observation predicates.

The empirical quotient is computed by grouping models whose reachable
observation sets are equal. Its canonical display label is a stable sorted
representation of the common reachable set; grouping itself uses actual set
equality.

## Interface refinement example

The runner also uses one eight-state world with four interfaces:

- an identity interface with eight observable classes;
- a paired-bucket interface with four classes;
- a binary-region interface with two classes;
- a relabeled identity interface with the same eight distinctions as the
  identity interface.

Explicit coarsening maps form the strict chain identity → paired buckets →
binary regions. The composed identity → region map illustrates transitivity.
Identity and relabeled identity refine one another, illustrating equal
observational resolution under a change of representation. The runner
enumerates collapsed state pairs and every entry of the induced quotient maps.

## Reproduce the results

From the repository root:

```bash
python3 -m venv simulations/.venv
source simulations/.venv/bin/activate
python -m pip install -r simulations/requirements.txt
python simulations/run_simulations.py
pytest simulations/tests
```

The runner deterministically overwrites its named outputs in
`simulations/results/`:

- `model_summary.csv`
- `multiplicity_summary.csv`
- `experiment_outcomes.csv`
- `predicate_profiles.csv`
- `empirical_quotient.csv`
- `nonidentifiable_properties.csv`
- `observation_fibers.csv`
- `interface_summary.csv`
- `refinement_summary.csv`
- `quotient_maps.csv`
- `collapsed_pairs.csv`
- `report.md`
- `refinement_report.md`
- six clearly labeled PNG plots

The Lean development can be rechecked independently with:

```bash
lake env lean BoundaryObserver.lean
lake build
```
