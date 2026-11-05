# Observer boundary manuscript revision

Prepared 5 November 2026 from the draft 0.9.1 source package. No GitHub commit or push has been made.

## Main corrections

| Original location | Correction in the revised article |
| --- | --- |
| Section 2.3, page 7 | A collision must involve distinct original states that actually reach the same intermediate value. A later map can be noninjective outside the reachable intermediate range without making the composite noninjective. Appendix J gives an explicit counterexample. |
| Theorem 8.8, page 25 | Added a nonempty observation space and a model class containing the identity model and its Boolean extension. Stated the quantifiers as failure of a criterion to decide decoder existence for each model, rather than deciding whether every model has a decoder. |
| Theorem 10.6, page 30 | Added the same assumptions. Distinguished global nonidentifiability from the stronger, false claim that every empirical class contains both decoder outcomes. Explained the empty reachable-set case. |
| Section 11.1, page 32 | The extension always has no decoder when the latent base is nonempty. Decoder status differs only when the base has a decoder. The nondecodable-base counterexample is proved and tested. |
| Section 9.5, page 28 | Replaced ordinary order-theoretic maximality language by the actual strict-cover existence result. Explained the Lean predicate and the strict self-cover on the natural numbers. No change to the valid Lean theorem. |
| Section 9.3 | Added the nonempty latent-space condition for failure of decoding in the countable extension. |
| Quotient factorization | Distinguished functions on reachable observations from total extensions to the observation codomain. Included the empty target-set exception and avoided implying algorithmic computability or numerical stability. |
| Empirical equivalence | Defined reachable-set equality near the front. Added a Bernoulli counterexample to equality of probability laws. |
| Temporal measurements | Added exact recovery from two samples in a simple known flow, with the error bound 2 eta / abs(T). This is a mathematical example, not biological evidence. |
| Neural interpretation | Explicitly separated spatial tuning, temporal trajectories, topology, and evidence of attraction. No attractor conclusion follows from this set theoretic theorem. |
| Theorem references | Fixed shared theorem counters so references identify Theorems and Corollaries correctly. |
| Differential geometry outlook | Clarified that nonzero connection coefficients can occur in flat space. Variable metric components alone do not establish curvature. |

## Organization

The main narrative contains the abstract, introduction, observation model and principal equations, main result, methods, findings, discussion, and conclusion. Detailed proofs, counterexamples, computational tables, operational architecture, related literature, and the broader hypotheses follow in appendices. The original introductory roadmap and repetitive interpretation/conclusion sections have been replaced; their substantive broader questions remain in the appendices.

The companion supplement retains implementation excerpts, the declaration concordance, complete principal tables, original simulation figures, and provenance. Wide-table headings now remain on the same pages as their tables. Two mathematical diagrams have more readable vector layouts.

## Verification and sources

- All 18 reference Python tests and 6 new regression tests pass.
- All 12 regenerated CSV files match the archived outputs byte for byte.
- The exact finite calculations involve no numerical integration or convergence claim. The temporal example uses rational arithmetic in the regression test and has an independent algebraic derivation.
- The pinned Lean source is unchanged. The repository CI records a successful build for commit `eb96b984ae999ee6cbc0aae33c2d501c46d9540f`. Lean was not rebuilt locally for this revision. New explanatory examples are not claimed as new Lean proofs.
- Checked the primary records used in the revised main argument: Rothenberg (1971), Hermann and Krener (1977), Locatello et al. (2019), and Gardner et al. (2022).
- Checked the arXiv records for Elshatlawy et al. and Abramsky et al. The four-author Elshatlawy citation is explicitly pinned to version 1; the Abramsky record links to version 2. The remaining background bibliography is retained, not represented as a newly completed full-text audit.
- Portable pdfLaTeX/BibTeX author-year typesetting replaces the unavailable original font and bibliography dependencies. Book editor metadata is retained in displayed notes. The bibliography content remains in `references.bib`.

## Exact changes

`EXACT_CHANGES.diff` is a unified diff against the original package for all changed textual source files and the new regression checks. Unchanged reference-code snapshots are omitted from the diff and identified by commit. Updated vector figures are identified by hashes in `verification/revision_manifest.json`.

The manuscript, supplement, and source package are prepared for review. Repository publication requires approval.
