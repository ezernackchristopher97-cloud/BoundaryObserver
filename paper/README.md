# Boundary Limited Observer Systems

Revised from draft 0.9.1 and published in this repository after author approval.
The initial review record is dated 5 November 2026 UTC, corresponding to
4 November in America/Chicago. A subsequent source check corrects the name
Giovanni di Sarra and includes the published correction to the cited oscillation
study. See `verification/source_followup.json` for the updated file hashes.

## Documents

- `Boundary_Limited_Observer_Systems_Draft_0_9_1.pdf`: revised article. The main narrative ends on page 5; appendices begin on page 6.
- `Boundary_Limited_Observer_Systems_Draft_0_9_1_Supplement.pdf`: updated computational and formal supplement.
- `REVISION_NOTES.md`: corrections, scope, and verification record.
- `EXACT_CHANGES.diff`: exact textual changes against the original source package.

## Build

A TeX Live installation with pdfLaTeX, BibTeX, latexmk, Times fonts, natbib, TikZ, and the packages listed in the document preambles is sufficient. No Biber or newtx installation is required.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error supplement.tex
```

The build produces `main.pdf` and `supplement.pdf`. The named PDFs above are the reviewed copies. The existing vector figures are included. Optional regeneration uses `generate_figures.py` with Matplotlib, pandas, and Graphviz; it ends by applying `draw_compact_diagrams.py`. `generate_appendices.py` regenerates the data and provenance tables with pandas.

## Reproduce the checks

Use Python 3.12 or another compatible Python 3 installation. Install the reference requirements into a virtual environment:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r verification/reference_code/simulations/requirements.txt
python -m pytest verification/reference_code/simulations/tests verification/test_scope_cases.py -q
python verification/verify_outputs.py
```

The expected results are 24 passing tests and 12 byte-identical CSV files. The output comparison writes `verification/output_verification.json`.

`verification/reference_code/simulations` is an unchanged snapshot of the reference implementation at commit `eb96b984ae999ee6cbc0aae33c2d501c46d9540f`. `verification/BoundaryObserver.lean` is the corresponding unchanged formal source. The added tests cover reachable collisions, already nondecodable bases, empty spaces, probability laws, temporal reconstruction and error amplification, and exhaustive decoder search over small finite maps.

The reference repository records successful Lean CI at https://github.com/ezernackchristopher97-cloud/BoundaryObserver/actions/runs/29449488270. No fresh local Lean build is claimed. Additional manuscript examples have written proofs and Python checks; they are not new Lean declarations.

## Scope

These are mathematical constructions and exhaustive finite calculations. They are not biological measurements. Equality of reachable observation sets does not imply equality of probability laws, temporal unobservability, physical hidden variables, or a universal limit on self-observation.
