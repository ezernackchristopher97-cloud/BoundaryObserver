# BoundaryObserver

**BoundaryObserver** is a Lean 4 formalization of observer limited inference, latent nonidentifiability, and empirical equivalence.

The central idea is that an observer may have complete access to everything available through an observation interface while still being unable to reconstruct the full latent structure that produced those observations.

The project separates three levels:

1. Latent states and generative structure
2. Observer accessible outputs
3. Experiments and properties defined only from those outputs

The main results show that observational completeness does not generally imply latent completeness.

## Core framework

The formalization introduces:

* Observer interfaces and observational equivalence
* Quantities that factor through an observation interface
* Exact decoders and conditions preventing exact reconstruction
* Generative models with latent states and accessible observations
* Admissible experiments and possible experimental outcomes
* Reachable observation sets
* Latent covers and strict latent covers
* Hidden factor and Boolean latent extensions
* Observation invariant properties and maps
* Complete predicate profiles
* Empirical equivalence classes and their quotient
* Realizable reachable observation sets

## Main results

The development proves that:

* States producing the same observation cannot be distinguished by an internal observer test.
* A noninjective observation map cannot possess a globally exact latent decoder.
* Observationally equivalent models produce the same possible outcomes under every admissible experiment.
* An inhabited generative model always admits a strict hidden extension with the same accessible observations.
* A strict hidden extension cannot possess an exact latent decoder.
* There is no maximal inhabited latent representation under strict hidden extension.
* Exact latent reconstructability is not invariant under observational equivalence.
* No admissible experiment can determine exact latent reconstructability for every model.
* Complete observer accessible predicate profiles characterize observational equivalence.
* Empirically identifiable properties are exactly the properties invariant under observational equivalence.
* Observation invariant properties and measurements factor uniquely through the empirical model quotient.
* The empirical model quotient is represented by realizable reachable observation sets.

## Synthesis theorem

The principal synthesis result is:

```lean
theorem boundaryLimitedObserver_synthesis
```

For every inhabited generative model and every admissible experiment, there exists a strict hidden extension that:

* belongs to the same empirical equivalence class,
* has the same reachable observation set,
* produces the same possible experimental outcomes,
* and does not admit exact reconstruction of its latent state.

This establishes a precise distinction between empirical equivalence and latent identity.

## Mathematical interpretation

The formal result is not that a particular hidden structure must exist.

It shows that, under the definitions used here, observer accessible information does not uniquely determine latent structure. Multiple models may remain empirically indistinguishable even when their internal state spaces differ.

The theorem therefore establishes a limit on identification, not a positive metaphysical conclusion about what lies beyond the observation interface.

## Project structure

The primary formal development is contained in:

```text
BoundaryObserver.lean
```

The file is organized progressively, beginning with observer interfaces and ending with empirical quotients, universal factorization results, and the boundary limited observer synthesis theorem.

## Building the project

The repository uses the Lean version specified in `lean-toolchain`.

From the repository directory, run:

```bash
lake update
lake build
```

To check the primary file directly in Visual Studio Code, open:

```text
BoundaryObserver.lean
```

with the Lean 4 extension installed.

## GitHub Actions

The repository includes GitHub Actions workflows for automated checking and release management.

A successful build verifies that the declarations and proofs compile under the configured Lean toolchain and project dependencies.

## Status

The main formal argument is substantially complete.

Current work includes:

* final proof cleanup,
* documentation refinement,
* removal of remaining style warnings,
* checking for accidental duplicated sections,
* and preparing the repository for a stable release.