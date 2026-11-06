# Boundary Limited Observer Systems

The article gives the recovery criterion and its consequences for finite observations. The supplement lists the formal declarations, simulation checks, and data sources.

## Documents

- `Boundary_Limited_Observer_Systems_Draft_0_9_1.pdf` contains the article and its mathematical appendices.
- `Boundary_Limited_Observer_Systems_Draft_0_9_1_Supplement.pdf` contains the computational and formal supplement.
- `REVISION_NOTES.md` records the source history. The hashes in `verification/source_followup.json` and `verification/round_two.json` identify the versions reviewed at those stages.
- `EXACT_CHANGES.diff` records the changes from the original source package.

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
python -m pytest verification/reference_code/simulations/tests verification/test_scope_cases.py verification/test_round_two.py -q
python verification/verify_outputs.py
```

The expected results are 26 passing tests and 12 byte-identical CSV files. The output comparison writes `verification/output_verification.json`.

`verification/reference_code/simulations` is an unchanged snapshot of the reference implementation at commit `eb96b984ae999ee6cbc0aae33c2d501c46d9540f`. `verification/BoundaryObserver.lean` is the corresponding unchanged formal source. The added tests cover reachable collisions, already nondecodable bases, empty spaces, probability laws, temporal reconstruction and error amplification, and exhaustive decoder search over small finite maps. The two second-round checks cover classification by reachable set
and identifiability from joint measurements.

GitHub records [successful Lean CI for the manuscript base](https://github.com/ezernackchristopher97-cloud/BoundaryObserver/actions/runs/41970754861). No fresh local Lean build is claimed. Additional manuscript examples have written proofs and Python checks; they are not new Lean declarations.

## Scope

These are mathematical constructions and exhaustive finite calculations. They are not biological measurements. Equality of reachable observation sets does not imply equality of probability laws, temporal unobservability, physical hidden variables, or a universal limit on self-observation.
