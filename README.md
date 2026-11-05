# BoundaryObserver

BoundaryObserver is a Lean 4 formalization of observer-limited inference. It
studies the distinction between an underlying state, the information exposed by
an observation interface, and the results obtainable by experiments restricted
to that exposed information.

The development formalizes latent nonidentifiability, empirical equivalence,
limits on exact decoding, hidden latent extensions, interface refinement,
observable quotients, empirical model quotients, and observation-only
experiments.

## Revised manuscript

The reviewed paper places its main argument, equations, methods, findings, and
conclusion in the first five pages. Detailed proofs and workings begin on page 6.

- [Article PDF](paper/Boundary_Limited_Observer_Systems_Draft_0_9_1.pdf)
- [Computational and formal supplement](paper/Boundary_Limited_Observer_Systems_Draft_0_9_1_Supplement.pdf)
- [LaTeX source and build instructions](paper/README.md)
- [Correction record](paper/REVISION_NOTES.md)
- [Exact changes against the original draft package](paper/EXACT_CHANGES.diff)

The paper directory contains the reviewed manuscript and its source package.
Its revision notes record the mathematical review and subsequent source checks.
The original diff and manifest describe the first reviewed version; the
[source follow-up record](paper/verification/source_followup.json) identifies
later citation corrections and their file hashes.

The corrected interpretation distinguishes reachable observation sets from
probability laws and temporal records. A Boolean hidden extension has no exact
decoder when its latent base is nonempty; decoder status differs from the base
only if the base is exactly decodable. The finite examples are mathematical
constructions and provide no empirical evidence of biological hidden variables
or neural attractors.

## Three levels of description

BoundaryObserver keeps three levels separate:

1. **Latent or world state** — the underlying `World` state or a model's
   `Latent` state.
2. **Observer-accessible observation** — the value in `Obs` returned by
   `observe`. Distinct latent states may produce the same observation.
3. **Observation-only experimental result** — the value returned by an
   admissible experiment `Obs → Result`. Such an experiment receives the
   accessible observation, not the latent state itself.

```text
latent state  --observe-->  accessible observation  --experiment-->  result
```

This separation makes it possible to state precisely when accessible
information is complete at the observation level while remaining incomplete
at the latent level.

## Claim boundary

The Lean results are conditional mathematical theorems about the models,
interfaces, maps, and experiments declared in the formalization. They establish
structural limits on inference under those definitions.

They do not prove that a particular metaphysical ontology is true, that any
specific real system has a hidden coordinate, or that inaccessible structure
must exist in nature. The Python simulations are finite computational
illustrations of selected definitions and theorems. They do not replace,
strengthen, or empirically validate the Lean proofs.

## Major formal definitions

The complete formal development is in
[`BoundaryObserver.lean`](BoundaryObserver.lean).

| Definition | Purpose |
| --- | --- |
| `ObserverInterface` | Specifies an accessible observation type and a map from world states to observations. |
| `ObsEq` | States that two world states produce the same accessible observation. |
| `FactorsThrough` | Expresses that a quantity is determined by a set function of the accessible observation; no algorithm or stability bound is asserted. |
| `HasExactDecoder` | Requires a decoder that is a left inverse of the observation map. |
| `InternalTest` | A Boolean test whose input is only an accessible observation. |
| `GenerativeModel` | Specifies a latent state type and a latent-to-observation map. |
| `Produces` | States that a model can produce a particular observation. |
| `ModelObsEq` | Identifies models with exactly the same reachable observations. |
| `AdmissibleExperiment` | An observation-only function `Obs → Result`. |
| `ExperimentOutcomeSet` | The set of all results an admissible experiment can produce under a model. |
| `ObservableQuotient` | Quotients world states by equality of their accessible observations. |
| `InterfaceRefines` | States that a set function of fine observations gives the coarse observations for every world state. |
| `StrictlyRefines` | A refinement that preserves strictly more distinctions than the coarse interface. |
| `LatentCover` | A surjective, observation-preserving projection from an extended latent model to a base model. |
| `StrictLatentCover` | A latent cover whose projection is noninjective, so the extension contains a genuine additional latent distinction. |
| `hiddenExtensionModel` | Adds a hidden factor to every latent state while ignoring that factor during observation. |
| `booleanExtensionModel` | The Boolean strict hidden extension used in the final synthesis theorem. |
| `finiteMultiplicityModel` | Adds a finite family of hidden copies to every latent state. |
| `EmpiricalModelQuotient` | Quotients generative models by `ModelObsEq`. |

The formalization also defines reachable-observation sets, complete
observation-predicate profiles, observation-invariant model properties and
measurements, realizable observation sets, and canonical maps to and from the
empirical model quotient.

## Main theorem family

The principal results include:

- **Factorized quantities respect observational equivalence.** If a quantity
  factors through an interface, it takes equal values on states with equal
  observations (`factorized_quantity_respects_obsEq`).
- **Noninjectivity prevents globally exact decoding.** A globally exact
  decoder implies injectivity, so a noninjective observation map has no such
  decoder (`no_exact_decoder_of_not_injective`).
- **Internal tests cannot distinguish observationally equivalent states.** Any
  observation-only Boolean test returns the same value on equal observations
  (`internal_test_cannot_distinguish_obsEq`).
- **Empirically equivalent models have identical admissible outcomes.** Models
  related by `ModelObsEq` have equal `ExperimentOutcomeSet`s for every
  admissible experiment (`modelObsEq_preserves_experimentOutcomeSet`).
- **Insufficient finite observation capacity forces collisions.** If a finite
  world has more states than its observation space, distinct world states
  produce the same observation (`finite_interface_has_collision`), and exact
  decoding is impossible (`finite_interface_has_no_exact_decoder`).
- **Compatible quantities descend through the observable quotient.** Every
  quantity respecting observational equivalence has a unique representation on
  `ObservableQuotient` (`observableQuotient_universal_property`).
- **Refinement induces a surjective quotient map.** A refinement maps the fine
  observable quotient onto the coarse quotient
  (`quotientMapOfRefinement_surjective`).
- **Strict refinement is irreversible and loses quotient injectivity.** Strict
  refinement prevents a reverse refinement and makes the induced quotient map
  noninjective (`strictlyRefines_prevents_reverse_refinement` and
  `strictlyRefines_quotientMap_not_injective`).
- **Mutual refinement induces a quotient equivalence.** Mutually refining
  interfaces have the same observational resolution and bijective quotient
  maps (`quotientMapOfMutualRefinement_bijective`).
- **Hidden extensions preserve accessible information while increasing latent
  multiplicity.** Boolean, finite, countable, and general hidden-factor
  constructions preserve reachable observations and admissible outcome sets
  while adding latent distinctions.
- **Exact latent reconstructability is not observationally invariant.** An
  exactly decodable model can have an observationally equivalent strict hidden
  extension that is not exactly decodable
  (`exactLatentDecoder_not_observationInvariant`).
- **Observation-invariant properties factor through the empirical quotient.**
  Model properties are observation-invariant exactly when they factor through
  `EmpiricalModelQuotient`
  (`observationInvariant_iff_factorsThroughEmpiricalModelQuotient`).
- **Observation-invariant measurements factor through the empirical quotient.**
  Arbitrary-valued invariant maps descend uniquely to the empirical quotient
  (`empiricalModelQuotient_map_universal_property` and
  `observationInvariantMap_iff_factorsThroughEmpiricalModelQuotient`).

The empirical model quotient is additionally shown to be equivalent to the
type of realizable reachable-observation sets.

## Synthesis theorem

The development culminates in the theorem:

```lean
theorem boundaryLimitedObserver_synthesis
```

For every inhabited generative model `M`—supplied by a latent state
`x : M.Latent`—and every admissible experiment, the theorem constructs a model
`Extended` such that:

- `Extended` is a strict latent cover of `M`;
- `Extended` belongs to the same empirical equivalence class as `M`;
- `Extended` has the same reachable observation set as `M`;
- the experiment has the same possible outcome set under both models; and
- `Extended` does not admit exact reconstruction of its latent state.

The construction uses `booleanExtensionModel`. It establishes a formal
distinction between complete agreement at the empirical boundary and identity
of latent representation.

## Mathematical interpretation

An observation map induces an equivalence relation on latent states: states are
identified when they generate the same accessible output. The observable
quotient retains exactly the distinctions available through that interface.
Likewise, `ModelObsEq` identifies generative models with the same reachable
observations, and `EmpiricalModelQuotient` retains models only up to that
empirical equivalence.

The hidden-extension results show that accessible observations and
observation-only outcomes need not determine latent cardinality, fiber size,
or exact latent reconstructability. This is a limit on identification within
the formal framework, not a positive claim about which latent ontology is
physically realized.

## Project structure

```text
BoundaryObserver.lean                 Complete Lean formalization
BoundaryObserver/Basic.lean           Lake library module
lakefile.toml                         Lean project and mathlib configuration
lean-toolchain                        Pinned Lean 4 toolchain
simulations/
  boundary_observer/                  Finite Python models and analyses
  tests/                              Pytest suite
  results/                            Generated CSV, Markdown, and PNG outputs
  run_simulations.py                  Reproducible command-line runner
  requirements.txt                    Python dependencies
  README.md                           Detailed simulation documentation
```

## Lean validation

From the repository root:

```bash
lake env lean BoundaryObserver.lean
lake build
```

The complete Lean file compiles under the pinned toolchain and contains no
unfinished `sorry` or `admit` proof commands.

## Executable simulations

The executable suite illustrates finite generative models, Boolean and finite
hidden extensions, observation fibers, admissible experiments, predicate
success and truth profiles, empirical classes, interface refinement, strict
coarsening, and induced finite quotient maps.

The current suite contains **24 passing tests**: the original 18 tests and six
regression checks for the manuscript assumptions and counterexamples.

To reproduce all generated outputs and run the tests:

```bash
python3 -m venv simulations/.venv
source simulations/.venv/bin/activate
python -m pip install -r simulations/requirements.txt
python simulations/run_simulations.py
python -m pytest simulations/tests -q
python paper/verification/verify_outputs.py
```

Documentation and generated reports:

- [Simulation guide](simulations/README.md)
- [Generative-model simulation report](simulations/results/report.md)
- [Interface-refinement simulation report](simulations/results/refinement_report.md)

The runner writes reproducible CSV summaries and six PNG plots to
`simulations/results/`.

The Lean theorems provide the general formal results. The Python suite
exhaustively calculates particular finite examples and verifies the executable
implementation; it does not replace or extend the logical scope of the proofs.

## Current status

The revised manuscript, supplement, exact correction record, and supporting
checks are included in `paper/`. All 24 Python tests pass, and the twelve
regenerated CSV outputs match the archived files byte for byte. The Lean source
is unchanged from the reference commit. The review inspected successful
repository CI; it did not perform a fresh local Lean build.
