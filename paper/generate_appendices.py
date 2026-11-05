from __future__ import annotations

from pathlib import Path
import json
import pandas as pd

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data" / "original_csv"
SECTIONS = ROOT / "sections"


def esc(value: object) -> str:
    s = str(value)
    replacements = {
        "\\": r"\textbackslash{}",
        "_": r"\_",
        "&": r"\&",
        "%": r"\%",
        "#": r"\#",
        "$": r"\$",
        "{": r"\{",
        "}": r"\}",
    }
    for a, b in replacements.items():
        s = s.replace(a, b)
    return s


model = pd.read_csv(DATA / "model_summary.csv")
exp = pd.read_csv(DATA / "experiment_outcomes.csv")
pred_s = pd.read_csv(DATA / "predicate_success_profiles.csv")
pred_t = pd.read_csv(DATA / "predicate_truth_profiles.csv")
emp = pd.read_csv(DATA / "empirical_quotient.csv")
nonid = pd.read_csv(DATA / "nonidentifiable_properties.csv")
interfaces = pd.read_csv(DATA / "interface_summary.csv")
refine = pd.read_csv(DATA / "refinement_summary.csv")
manifest = json.loads((ROOT / "data_manifest.json").read_text())

lines: list[str] = []
lines += [
    r"\section{Repository data tables}",
    r"\label{app:fulldata}",
    "",
    r"This appendix prints the principal committed finite records. The complete machine readable files are included under \texttt{data/original\_csv/}. No values in these tables were inferred from figure positions.",
    "",
    r"\subsection{Complete model summary}",
    r"\begin{landscape}",
    r"\scriptsize",
    r"\begin{longtable}{@{}lrrrrrrccc@{}}",
    r"\caption{Complete \texttt{model\_summary.csv}}\label{tab:fullmodelsummary}\\",
    r"\toprule",
    r"Model & Latent & Reachable & Avg fiber & Max fiber & Collisions & Multiplicity & Injective & Decoder & Hidden kind \\",
    r"\midrule",
    r"\endfirsthead",
    r"\toprule",
    r"Model & Latent & Reachable & Avg fiber & Max fiber & Collisions & Multiplicity & Injective & Decoder & Hidden kind \\",
    r"\midrule",
    r"\endhead",
]
for _, r in model.iterrows():
    lines.append(
        f"{esc(r['model'])} & {int(r['latent_state_count'])} & {int(r['reachable_observation_count'])} & "
        f"{float(r['average_fiber_size']):.2f} & {int(r['maximum_fiber_size'])} & {int(r['latent_collision_count'])} & "
        f"{int(r['hidden_multiplicity'])} & {esc(r['observation_function_injective'])} & "
        f"{esc(r['exact_latent_decoder_possible'])} & {esc(r['hidden_factor_kind'])} \\\\"
    )
lines += [r"\bottomrule", r"\end{longtable}", r"\end{landscape}", ""]

lines += [
    r"\subsection{Complete experiment outcome records}",
    r"\small",
    r"\begin{longtable}{@{}llrlrc@{}}",
    r"\caption{Complete \texttt{experiment\_outcomes.csv}}\label{tab:fullexperiments}\\",
    r"\toprule",
    r"Experiment & Model & Multiplicity & Possible outcomes & Count & Matches base \\",
    r"\midrule",
    r"\endfirsthead",
    r"\toprule",
    r"Experiment & Model & Multiplicity & Possible outcomes & Count & Matches base \\",
    r"\midrule",
    r"\endhead",
]
for _, r in exp.iterrows():
    lines.append(
        f"{esc(r['experiment'])} & {esc(r['model'])} & {int(r['hidden_multiplicity'])} & "
        f"{esc(r['possible_outcomes'])} & {int(r['outcome_count'])} & {esc(r['matches_base_outcomes'])} \\\\"
    )
lines += [r"\bottomrule", r"\end{longtable}", ""]

lines += [
    r"\subsection{Predicate records}",
    r"The existential profile file contains 21 model and predicate rows. The truth profile file contains the corresponding 21 complete truth table rows. Every comparison column is true. The three unique base truth tables are printed below.",
    r"\begin{table}[H]",
    r"\centering",
    r"\caption{Unique predicate truth tables from \texttt{predicate\_truth\_profiles.csv}}",
    r"\begin{tabularx}{\textwidth}{@{}lXcc@{}}",
    r"\toprule",
    r"Predicate & Truth table & Success in base & All seven models match \\",
    r"\midrule",
]
base_t = pred_t[pred_t["model"] == "injective_base"]
base_s = pred_s[pred_s["model"] == "injective_base"].set_index("predicate")
for _, r in base_t.iterrows():
    pred = r["predicate"]
    lines.append(
        f"{esc(pred)} & {esc(r['truth_table'])} & {esc(base_s.loc[pred, 'can_succeed'])} & True \\\\"
    )
lines += [r"\bottomrule", r"\end{tabularx}", r"\end{table}", ""]

lines += [
    r"\subsection{Empirical quotient and varying properties}",
    r"\begin{table}[H]",
    r"\centering",
    r"\caption{Complete \texttt{empirical\_quotient.csv}}",
    r"\scriptsize",
    r"\begin{tabularx}{\textwidth}{@{}cXlXc@{}}",
    r"\toprule",
    r"Class & Reachable set & Latent cardinalities & Models & Multiple cardinalities \\",
    r"\midrule",
]
for _, r in emp.iterrows():
    lines.append(
        f"{int(r['empirical_class'])} & {esc(r['canonical_reachable_observations'])} & "
        f"{esc(r['latent_cardinalities'])} & {esc(r['model_names'])} & {esc(r['contains_multiple_latent_cardinalities'])} \\\\"
    )
lines += [r"\bottomrule", r"\end{tabularx}", r"\end{table}", ""]

lines += [
    r"\begin{table}[H]",
    r"\centering",
    r"\caption{Complete \texttt{nonidentifiable\_properties.csv}}",
    r"\begin{tabularx}{\textwidth}{@{}Xccccc@{}}",
    r"\toprule",
    r"Property & Base & Extension & Varies & Reach equal & Outcomes equal \\",
    r"\midrule",
]
for _, r in nonid.iterrows():
    lines.append(
        f"{esc(r['property'])} & {esc(r['base_value'])} & {esc(r['extension_value'])} & "
        f"{esc(r['varies_within_empirical_class'])} & {esc(r['reachable_observations_equal'])} & "
        f"{esc(r['all_tested_experiment_outcomes_equal'])} \\\\"
    )
lines += [r"\bottomrule", r"\end{tabularx}", r"\end{table}", ""]

lines += [
    r"\subsection{Complete interface and refinement summaries}",
    r"\begin{table}[H]",
    r"\centering",
    r"\caption{Complete \texttt{interface\_summary.csv}}",
    r"\begin{tabularx}{\textwidth}{@{}lrrrXrc@{}}",
    r"\toprule",
    r"Interface & World & Codomain & Reachable & Reachable values & Quotient & Injective \\",
    r"\midrule",
]
for _, r in interfaces.iterrows():
    lines.append(
        f"{esc(r['interface'])} & {int(r['world_state_count'])} & {int(r['observation_space_count'])} & "
        f"{int(r['reachable_observation_count'])} & {esc(r['reachable_observations'])} & "
        f"{int(r['observable_quotient_size'])} & {esc(r['observation_function_injective'])} \\\\"
    )
lines += [r"\bottomrule", r"\end{tabularx}", r"\end{table}", ""]

lines += [
    r"\begin{landscape}",
    r"\scriptsize",
    r"\begin{longtable}{@{}lllrrrrcccc@{}}",
    r"\caption{Selected complete fields from \texttt{refinement\_summary.csv}}\label{tab:fullrefinement}\\",
    r"\toprule",
    r"Refinement & Fine & Coarse & Fine Q & Coarse Q & Collapsed & Strict & Reverse & Surjective & Injective & Bijective \\",
    r"\midrule",
    r"\endfirsthead",
    r"\toprule",
    r"Refinement & Fine & Coarse & Fine Q & Coarse Q & Collapsed & Strict & Reverse & Surjective & Injective & Bijective \\",
    r"\midrule",
    r"\endhead",
]
for _, r in refine.iterrows():
    lines.append(
        f"{esc(r['refinement'])} & {esc(r['fine_interface'])} & {esc(r['coarse_interface'])} & "
        f"{int(r['fine_quotient_size'])} & {int(r['coarse_quotient_size'])} & {int(r['collapsed_world_pair_count'])} & "
        f"{esc(r['strict_refinement'])} & {esc(r['reverse_refinement_exists'])} & "
        f"{esc(r['quotient_map_surjective'])} & {esc(r['quotient_map_injective'])} & {esc(r['quotient_map_bijective'])} \\\\"
    )
lines += [r"\bottomrule", r"\end{longtable}", r"\end{landscape}", ""]

lines += [
    r"The files \texttt{observation\_fibers.csv}, \texttt{quotient\_maps.csv}, and \texttt{collapsed\_pairs.csv} contain the unaggregated fiber, class map, and pair records. They are included in the package because printing every latent state tuple would add length without adding a distinct result.",
]
(SECTIONS / "app_b_full_data.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")

# Provenance appendix
lines = [
    r"\section{Data provenance and file integrity}",
    r"\label{app:provenance}",
    "",
    r"The manifest was generated from the files included with this paper. Git blob hashes were calculated with \texttt{git hash-object}. SHA256 hashes were calculated from the file bytes. The full hashes are stored in \texttt{data\_manifest.json}; abbreviated Git blob hashes are printed below.",
    "",
    r"\begin{longtable}{@{}lrrl@{}}",
    r"\caption{Committed CSV provenance}\label{tab:manifest}\\",
    r"\toprule",
    r"File & Data rows & Git blob SHA prefix & Role \\",
    r"\midrule",
    r"\endfirsthead",
    r"\toprule",
    r"File & Data rows & Git blob SHA prefix & Role \\",
    r"\midrule",
    r"\endhead",
]
roles = {
    "model_summary.csv": "All finite model summaries",
    "multiplicity_summary.csv": "Hidden multiplicity family",
    "experiment_outcomes.csv": "Possible outcome sets",
    "predicate_success_profiles.csv": "Existential predicate profiles",
    "predicate_truth_profiles.csv": "Complete finite truth profiles",
    "empirical_quotient.csv": "Finite empirical classes",
    "nonidentifiable_properties.csv": "Latent property variation",
    "observation_fibers.csv": "Unaggregated observation fibers",
    "interface_summary.csv": "Finite interface summaries",
    "refinement_summary.csv": "Refinement and quotient map summary",
    "quotient_maps.csv": "Unaggregated quotient map entries",
    "collapsed_pairs.csv": "Unaggregated strict collapse records",
}
for name, info in manifest["csv_files"].items():
    lines.append(
        f"{esc(name)} & {info['rows_excluding_header']} & \\texttt{{{info['git_blob_sha'][:12]}}} & {esc(roles.get(name,''))} \\\\"
    )
lines += [r"\bottomrule", r"\end{longtable}", ""]
lines += [
    r"The original repository PNG files are also hash recorded. The vector paper figures are generated products and are not represented as committed repository PNGs. The collision plot is explicitly marked supplemental because no collision PNG is produced by the current repository runner.",
    "",
    r"\subsection{Validation record}",
    r"\begin{table}[H]",
    r"\centering",
    r"\caption{Repository validation record used by the paper}",
    r"\begin{tabularx}{\textwidth}{@{}lX@{}}",
    r"\toprule",
    r"Check & Recorded result \\",
    r"\midrule",
    r"Local Lean compilation in this revision & Not rerun \\",
    r"Repository Lean CI & Successful for the pinned commit; \url{https://github.com/ezernackchristopher97-cloud/BoundaryObserver/actions/runs/29449488270} \\",
    r"Unfinished proof commands & None in project source \\",
    r"Simulation runner & Completed all Boolean, multiplicity, experiment, predicate, quotient, and refinement assertions \\",
    r"Automated tests & 18 repository tests and 6 revision regression tests passed \\",
    r"CSV reproduction & All 12 files byte identical to the archived outputs \\",
    r"Repository state & Commit \RepoCommit \\",
    r"\bottomrule",
    r"\end{tabularx}",
    r"\end{table}",
]
(SECTIONS / "app_d_provenance.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")


# Keep headings with the wide tables they introduce.
p = SECTIONS / 'app_b_full_data.tex'
s = p.read_text()
first = s.index(r'\begin{landscape}')
s = r'\begin{landscape}' + '\n' + s[:first] + s[first:].replace(r'\begin{landscape}', '', 1)
a = s.index(r'\subsection{Complete experiment outcome records}')
b = s.index(r'\subsection{Predicate records}', a)
block = s[a:b].replace(r'\small', r'\scriptsize', 1)
block = block.replace(r'\begin{longtable}{@{}llrlrc@{}}',
    r'\begin{longtable}{@{}p{0.13\linewidth}p{0.27\linewidth}rp{0.25\linewidth}rc@{}}')
s = s[:a] + r'\begin{landscape}' + '\n' + block + r'\end{landscape}' + '\n\n' + s[b:]
p.write_text(s)
