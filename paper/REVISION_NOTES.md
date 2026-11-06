# Observer boundary manuscript revision

Initially prepared 5 November 2026 UTC from the draft 0.9.1 source package,
before any repository commit or push. Publication and subsequent checks are
recorded at the end of this document.

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

The initial manuscript, supplement, and source package were subsequently
approved and published in commit `ae573f0e6f66e48721bf1c0aded5860f2767b048`.

## Continued source review

The GitHub Lean Action CI for that commit completed successfully:
https://github.com/ezernackchristopher97-cloud/BoundaryObserver/actions/runs/41968768664

The first author of the cited grid-cell oscillation study is Giovanni di Sarra,
not Giordano Di Sarra. The bibliography now uses the publisher's name and
includes the published correction, DOI `10.1371/journal.pcbi.1013623`.
Appendix N identifies that notice as a replacement of duplicated panels in the
synthetic calibration figure. No biological conclusion is inferred from the
present paper's finite mathematical calculations.

The article remains 64 pages, with the main narrative ending on page 5. The
updated PDF compiled without unresolved references or overfull boxes, and all
changed pages were rendered and inspected. Formal source and Python tests are
unchanged. `SOURCE_FOLLOWUP.diff` records the source changes after the approved
commit; `verification/source_followup.json` records the new file hashes.

## Second editorial and mathematical review

The second round starts at `340d70b83a77568ebef0df3074349fdd4a683fe9`. The
article now opens with inference from a report and distinguishes recovering a
specified target from deciding whether an entire latent state is recoverable.
For each nonempty reachable set, its inclusion and Boolean extension witness
opposite decoder statuses in any class containing both. The proof handles
the empty reachable set separately. The discussion derives the necessary and
sufficient separation condition for a second measurement to identify a target.

The modulo-three construction is compared with the other models in a common
six-label observation space. The finite comparisons include seven representations
(including the base) and four processing rules. Individual pair and quotient-map
records are in the CSV files. The supplement now typesets its Python excerpts
directly from the pinned implementation and gives the commands needed to repeat
the checks. The two new finite checks cover small reachable sets and all 4,096
triples of binary reports, readings, and targets on a four-state source.

Corrected the bylines for [Rickles et al.](https://arxiv.org/abs/2308.16068v2),
[Tononi et al.](https://www.nature.com/articles/s41593-025-01880-y), and
[Robinson et al.](https://pubmed.ncbi.nlm.nih.gov/41343515/). The Robinson article
is a study protocol. The article uses the [simultaneous grid-cell study](https://doi.org/10.1038/s41586-021-04268-7)
for evidence about measured population geometry. Every cited key resolves locally.
The external source review covers selected references, not the full background bibliography.

The 26 manuscript checks and the 24 repository simulation tests pass in their
respective suites. All twelve regenerated CSV files match the archived bytes.
All 41 declaration names in the supplement occur in the Lean file. The
[successful CI build](https://github.com/ezernackchristopher97-cloud/BoundaryObserver/actions/runs/41970754861)
checked the manuscript base. The new corollaries have direct proofs and finite
checks. No new local Lean build was performed. Earlier manifests and diffs remain
historical records. Current hashes and build details appear in
`verification/round_two.json`.
