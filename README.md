# BoundaryObserver

BoundaryObserver is a Lean 4 formalization of observer-limited inference. It
studies what can and cannot be recovered when an underlying state is available
only through an observation boundary. The development covers latent
nonidentifiability, empirical equivalence, hidden-state extensions, interface
refinement, observable and empirical quotient constructions, and the behavior
of observation-only experiments.

The formal results are conditional mathematical statements about the declared
interfaces and models. They do not establish a metaphysical thesis, infer a
particular ontology from data, or treat finite simulations as evidence for
claims outside the framework.

## Three levels of the framework

BoundaryObserver separates three levels that should not be conflated:

1. **Latent or world state** — the underlying state in `World`, or the latent
   state of a `GenerativeModel`.
2. **Observer-accessible output** — the value in `Obs` produced by `observe`.
   States with equal outputs are observationally equivalent at that interface.
3. **Observation-only experiment** — a function `Obs → Result`. Its possible
   outcomes depend on reachable observations, not on inaccessible distinctions
   between latent states in the same observation fiber.

In compact form:

```text
latent state  --observe-->  accessible observation  --experiment-->  result
```

## Core formal definitions

The main formalization is [`BoundaryObserver.lean`](BoundaryObserver.lean).
Important definitions include:

| Definition | Role |
| --- | --- |
| `ObserverInterface` | An observation type and a map from world states to accessible observations. |
| `ObsEq` | Equality of the observations produced by two world states. |
| `FactorsThrough` | An accessible quantity factors through the observation map. |
| `HasExactDecoder` | A decoder is a left inverse of the observation map. |
| `InternalTest` | A Boolean test receiving only accessible observations. |
| `GenerativeModel` | A latent state type together with a latent-to-observation map. |
| `Produces` | Reachability of an accessible observation under a model. |
| `ModelObsEq` | Equality of the reachable observation sets of two models. |
| `AdmissibleExperiment` | An observation-only function `Obs → Result`. |
| `ExperimentOutcomeSet` | The set of results an experiment can produce under a model. |
| `ObservableQuotient` | World states quotiented by equality of their observations. |
| `InterfaceRefines` | A fine observation can be mapped to a coarse observation while preserving observations of every world state. |
| `StrictlyRefines` | A refinement that loses at least one distinction. |
| `LatentCover` | A surjective, observation-preserving projection from an extended model to a base model. |
| `hiddenExtensionModel` | A product extension whose hidden coordinate is ignored by observation. |
| `finiteMultiplicityModel` | A finite hidden-factor extension with `n + 1` copies per base latent state. |

## Principal formal results

The Lean development proves, among other results:

- quantities that factor through an interface are constant on observational
  equivalence classes (`factorized_quantity_respects_obsEq`);
- an exact decoder implies injectivity, so a noninjective observation map has
  no globally exact decoder (`no_exact_decoder_of_not_injective`);
- observation-only tests cannot distinguish observationally equivalent states
  (`internal_test_cannot_distinguish_obsEq`);
- observationally equivalent generative models have equal possible outcome
  sets for every admissible experiment
  (`modelObsEq_preserves_experimentOutcomeSet`);
- a finite interface with fewer observations than world states has a collision
  and no exact decoder (`finite_interface_has_collision` and
  `finite_interface_has_no_exact_decoder`);
- the observable quotient is equivalent to the reachable range of the
  observation map, and compatible quantities descend uniquely to that
  quotient (`observableQuotient_universal_property`);
- accessible factorization is monotone under interface refinement
  (`factorization_monotone_under_refinement`);
- a refinement induces a surjective map from the fine observable quotient to
  the coarse quotient (`quotientMapOfRefinement_surjective`);
- strict refinement prevents reverse refinement and produces a noninjective
  quotient map (`strictlyRefines_prevents_reverse_refinement` and
  `strictlyRefines_quotientMap_not_injective`);
- mutual refinement gives a bijection between observable quotients
  (`quotientMapOfMutualRefinement_bijective`);
- Boolean and general inhabited hidden-factor extensions preserve reachable
  observations while introducing latent collisions and preventing exact
  reconstruction;
- arbitrary finite latent multiplicity is compatible with the same accessible
  outcomes (`arbitrary_finite_latent_multiplicity_is_empirically_hidden`).

### The synthesis result

The project-level synthesis, referred to in the project documentation as
`boundaryLimitedObserver_synthesis`, combines the central consequences:
observer-accessible quantities and experiments factor through the observation
boundary; noninjective boundaries prevent exact latent recovery; empirically
equivalent models agree on all admissible outcome sets; and hidden extensions
can vary latent multiplicity without varying the accessible observations.

In the current checked-in [`BoundaryObserver.lean`](BoundaryObserver.lean),
these components are exposed through the named theorem family above rather
than through a separate Lean declaration with the exact identifier
`boundaryLimitedObserver_synthesis`.

## Mathematical interpretation and claim boundary

An observation map determines an equivalence relation: two latent states are
equivalent exactly when they produce the same accessible observation. The
observable quotient retains the distinctions visible through the interface and
forgets distinctions within each observation fiber. An admissible experiment
acts after this boundary, so its set of possible outcomes is fixed by the
reachable observations.

Hidden-factor models demonstrate formal underdetermination: different latent
cardinalities, fiber sizes, decoder properties, and hidden coordinates can be
compatible with one reachable observation set. This is a theorem about the
specified mathematical structures. It is not an empirical proof that any
particular real system has hidden factors, not a probabilistic identification
result, and not confirmation of a metaphysical claim.

## Project structure

```text
BoundaryObserver.lean                 Main Lean formalization
BoundaryObserver/Basic.lean           Lake library module
lakefile.toml                         Lean project configuration
lean-toolchain                        Pinned Lean toolchain
simulations/
  boundary_observer/                  Finite Python model implementation
  tests/                              Pytest verification suite
  results/                            Reproducible CSV, Markdown, and PNG output
  run_simulations.py                  Command-line simulation runner
  requirements.txt                    Minimal Python dependencies
  README.md                           Detailed simulation documentation
```

## Building the Lean project

From the repository root:

```bash
lake env lean BoundaryObserver.lean
lake build
```

Both commands check the formal development. The main file contains no `sorry`
or `admit` declarations.

## Executable simulations

The Python suite gives inspectable finite examples of the formal structures:
injective and noninjective models, Boolean and finite-multiplicity hidden
extensions, observation-only experiments, existential predicate-success
profiles, complete predicate truth tables, empirical classes, and interface
refinement maps.

- [Simulation guide](simulations/README.md)
- [Generative-model simulation report](simulations/results/report.md)
- [Interface-refinement simulation report](simulations/results/refinement_report.md)

To reproduce the Python outputs and tests:

```bash
python3 -m venv simulations/.venv
source simulations/.venv/bin/activate
python -m pip install -r simulations/requirements.txt
python simulations/run_simulations.py
pytest simulations/tests
```

The runner writes deterministic CSV summaries, Markdown reports, and six PNG
plots to `simulations/results/`.

## Proofs versus illustrations

The Lean theorems quantify over the types, functions, models, and experiments
stated in their declarations and provide the general formal guarantees of this
project. The Python suite exhaustively computes selected finite instances. Its
tests and generated outputs illustrate the formal constructions and guard the
executable implementation, but they neither replace nor strengthen the Lean
proofs.
