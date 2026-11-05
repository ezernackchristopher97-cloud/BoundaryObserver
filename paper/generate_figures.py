from __future__ import annotations

from pathlib import Path
import hashlib
import json
import subprocess

import matplotlib.pyplot as plt
import pandas as pd

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data" / "original_csv"
FIG = ROOT / "figures"
FIG.mkdir(parents=True, exist_ok=True)

plt.rcParams.update(
    {
        "font.size": 10,
        "axes.titlesize": 12,
        "axes.labelsize": 10,
        "legend.fontsize": 8,
        "figure.dpi": 160,
        "savefig.dpi": 300,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
    }
)


def save(fig: plt.Figure, stem: str) -> None:
    fig.tight_layout()
    fig.savefig(FIG / f"{stem}.pdf", bbox_inches="tight")
    fig.savefig(FIG / f"{stem}.svg", bbox_inches="tight")
    plt.close(fig)


mult = pd.read_csv(DATA / "multiplicity_summary.csv")
exp = pd.read_csv(DATA / "experiment_outcomes.csv")
interfaces = pd.read_csv(DATA / "interface_summary.csv")
refs = pd.read_csv(DATA / "refinement_summary.csv")

# These six plots reproduce the data selection, axes, titles, labels, and line/bar
# logic of simulations/run_simulations.py at repository commit
# eb96b984ae999ee6cbc0aae33c2d501c46d9540f. Only the output format is changed
# from raster PNG to vector PDF/SVG.
for metric, ylabel, title, stem in [
    (
        "latent_state_count",
        "Latent state count",
        "Latent states grow with hidden multiplicity",
        "repo_latent_state_count_vs_hidden_multiplicity",
    ),
    (
        "reachable_observation_count",
        "Reachable observation count",
        "Reachable observations remain fixed",
        "repo_reachable_observation_count_vs_hidden_multiplicity",
    ),
    (
        "maximum_fiber_size",
        "Maximum fiber size",
        "Maximum fiber size grows with hidden multiplicity",
        "repo_maximum_fiber_size_vs_hidden_multiplicity",
    ),
]:
    fig, ax = plt.subplots(figsize=(7.2, 4.6))
    ax.plot(mult["hidden_multiplicity"], mult[metric], marker="o", linewidth=2)
    ax.set_xlabel("Hidden multiplicity")
    ax.set_ylabel(ylabel)
    ax.set_title(title)
    ax.set_xticks(mult["hidden_multiplicity"])
    ax.grid(alpha=0.3)
    save(fig, stem)

model_names = {
    "injective_base_1_fold_extension",
    "injective_base_2_fold_extension",
    "injective_base_3_fold_extension",
    "injective_base_5_fold_extension",
    "injective_base_8_fold_extension",
}
experiment_order = [
    "identity",
    "threshold_at_3",
    "categorical_partition",
    "compressed_width_2",
]
styles = (
    {"marker": "o", "linewidth": 2.2, "linestyle": "-"},
    {"marker": "s", "linewidth": 2.2, "linestyle": "--"},
    {"marker": "^", "linewidth": 5.0, "linestyle": "-"},
    {"marker": "D", "linewidth": 2.0, "linestyle": ":"},
)
fig, ax = plt.subplots(figsize=(7.2, 4.6))
for name, style in zip(experiment_order, styles, strict=True):
    selected = exp[(exp["experiment"] == name) & exp["model"].isin(model_names)].copy()
    selected = selected.sort_values("hidden_multiplicity")
    ax.plot(
        selected["hidden_multiplicity"],
        selected["outcome_count"],
        label=name,
        **style,
    )
ax.set_xlabel("Hidden multiplicity")
ax.set_ylabel("Possible experiment outcome count")
ax.set_title("Observation-only outcomes remain fixed")
ax.set_xticks(sorted(mult["hidden_multiplicity"].unique()))
ax.grid(alpha=0.3)
ax.legend(fontsize=8)
save(fig, "repo_experiment_outcome_count_vs_hidden_multiplicity")

labels = interfaces["interface"].str.replace("_interface", "", regex=False)
sizes = interfaces["observable_quotient_size"].astype(int)
fig, ax = plt.subplots(figsize=(8.0, 4.8))
bars = ax.bar(labels, sizes, color=("#2563eb", "#7c3aed", "#db2777", "#0891b2"))
ax.bar_label(bars, padding=3)
ax.set_ylabel("Observable quotient class count")
ax.set_title("Finite interfaces retain different numbers of distinctions")
ax.set_ylim(0, sizes.max() + 1.5)
ax.grid(axis="y", alpha=0.25)
ax.tick_params(axis="x", rotation=15)
save(fig, "repo_observable_quotient_size_by_interface")

labels = refs["refinement"].str.replace("_to_", " -> ", regex=False)
counts = refs["collapsed_world_pair_count"].astype(int)
fig, ax = plt.subplots(figsize=(8.0, 4.8))
bars = ax.barh(labels, counts, color="#c2410c")
ax.bar_label(bars, padding=3)
ax.set_xlabel("Pairs distinguished by fine and identified by coarse")
ax.set_title("Collapsed pairs under finite coarsening")
ax.set_xlim(0, counts.max() + 2)
ax.grid(axis="x", alpha=0.25)
save(fig, "repo_collapsed_pairs_by_refinement")

# Supplemental figure derived from an existing repository CSV column. The current
# repository runner does not write a corresponding PNG, so it is labeled as a
# supplemental paper figure rather than a repository plot.
fig, ax = plt.subplots(figsize=(7.2, 4.6))
ax.plot(
    mult["hidden_multiplicity"],
    mult["latent_collision_count"],
    marker="o",
    linewidth=2,
)
ax.set_xlabel("Hidden multiplicity")
ax.set_ylabel("Unordered latent collision pairs")
ax.set_title("Latent collisions increase with hidden multiplicity")
ax.set_xticks(mult["hidden_multiplicity"])
ax.grid(alpha=0.3)
save(fig, "supplemental_collision_count_from_repository_csv")

# Conceptual diagrams. These diagrams show only mathematical objects and
# relations explicitly developed in the repository. They are not simulation
# outputs and do not introduce additional empirical claims.
dots: dict[str, str] = {
    "concept_recursive_architecture": r'''
digraph G {
  graph [rankdir=TB, bgcolor="transparent", pad="0.12", nodesep="0.30", ranksep="0.38", splines=polyline];
  node [shape=box, style="rounded,filled", fillcolor="white", color="#334155", fontname="Helvetica", fontsize=10.5, margin="0.18,0.09", width=3.2];
  edge [color="#475569", penwidth=1.25, arrowsize=0.75, fontname="Helvetica", fontsize=9];
  S0 [label="Physical or model state  S(t)"];
  A [label="Apparatus, intervention, and sampling  A_i"];
  E [label="Finite encoding or reconstruction  E_i"];
  O [label="Observer accessible representation  O_i"];
  L [label="Reportable model, estimate, or claim  L_i"];
  P [label="Prediction, intervention, or next experiment  P_i"];
  S1 [label="Subsequent state or observation  S(t + Delta t)"];
  S0 -> A -> E -> O -> L -> P -> S1;
  S1 -> A [constraint=false, label="next cycle", style=dashed, minlen=2];
}
''',
    "concept_observation_fibers": r'''
digraph G {
  graph [rankdir=LR, bgcolor="transparent", pad="0.12", nodesep="0.24", ranksep="0.72", splines=spline];
  node [fontname="Helvetica", fontsize=10];
  edge [color="#475569", penwidth=1.2, arrowsize=0.72];
  subgraph clusterX {
    label="Source or latent states X"; color="#94a3b8"; style="rounded";
    x1 [shape=circle, label="x1"]; x2 [shape=circle, label="x2"]; x3 [shape=circle, label="x3"];
    x4 [shape=circle, label="x4"]; x5 [shape=circle, label="x5"]; x6 [shape=circle, label="x6"];
  }
  subgraph clusterO {
    label="Accessible observations O"; color="#94a3b8"; style="rounded";
    o1 [shape=box, style="rounded,filled", fillcolor="white", label="o1\nfiber {x1,x2}"];
    o2 [shape=box, style="rounded,filled", fillcolor="white", label="o2\nfiber {x3}"];
    o3 [shape=box, style="rounded,filled", fillcolor="white", label="o3\nfiber {x4,x5,x6}"];
  }
  x1 -> o1; x2 -> o1; x3 -> o2; x4 -> o3; x5 -> o3; x6 -> o3;
}
''',
    "concept_observable_quotient": r'''
digraph G {
  graph [rankdir=TB, bgcolor="transparent", pad="0.14", nodesep="0.55", ranksep="0.50", splines=polyline];
  node [shape=box, style="rounded,filled", fillcolor="white", color="#334155", fontname="Helvetica", fontsize=10, margin="0.16,0.10"];
  edge [color="#475569", penwidth=1.25, arrowsize=0.75, fontname="Helvetica", fontsize=9];
  X [label="World states X"];
  Q [label="Observable quotient\nX / observational equivalence"];
  R [label="Reachable observation range\nim(pi) subset O"];
  V [label="Values of an accessible quantity\nV"];
  X -> Q [label="class map"];
  Q -> R [label="canonical bijection"];
  Q -> V [label="unique descended map"];
  X -> V [label="fiber constant map f", style=dashed, constraint=false];
}
''',
    "concept_interface_refinement": r'''
digraph G {
  graph [rankdir=TB, bgcolor="transparent", pad="0.14", nodesep="0.52", ranksep="0.48", splines=polyline];
  node [shape=box, style="rounded,filled", fillcolor="white", color="#334155", fontname="Helvetica", fontsize=10, margin="0.15,0.10"];
  edge [color="#475569", penwidth=1.25, arrowsize=0.75, fontname="Helvetica", fontsize=9];
  X [label="Common world X"];
  OF [label="Fine observations O_F"];
  OC [label="Coarse observations O_C"];
  QF [label="Fine quotient X / ~F"];
  QC [label="Coarse quotient X / ~C"];
  {rank=same; OF; OC;}
  {rank=same; QF; QC;}
  X -> OF [label="pi_F"];
  X -> OC [label="pi_C"];
  OF -> OC [label="coarsen c\npi_C = c o pi_F"];
  X -> QF [label="class_F"];
  X -> QC [label="class_C"];
  QF -> QC [label="induced surjection"];
}
''',
    "concept_hidden_extension": r'''
digraph G {
  graph [rankdir=LR, bgcolor="transparent", pad="0.14", nodesep="0.60", ranksep="0.55", splines=polyline];
  node [shape=box, style="rounded,filled", fillcolor="white", color="#334155", fontname="Helvetica", fontsize=10.5, margin="0.18,0.11"];
  edge [color="#475569", penwidth=1.25, arrowsize=0.75, fontname="Helvetica", fontsize=9];
  XH [label="Extended latent space\nX_M x H"];
  X [label="Base latent space\nX_M"];
  O [label="Accessible observation space\nO"];
  XH -> X [label="surjective projection\np(x,h)=x"];
  X -> O [label="pi_M"];
  XH -> O [label="pi_MH(x,h)=pi_M(x)", style=dashed, constraint=false];
}
''',
    "concept_empirical_quotient": r'''
digraph G {
  graph [rankdir=TB, bgcolor="transparent", pad="0.14", nodesep="0.55", ranksep="0.48", splines=polyline];
  node [shape=box, style="rounded,filled", fillcolor="white", color="#334155", fontname="Helvetica", fontsize=10, margin="0.16,0.10"];
  edge [color="#475569", penwidth=1.25, arrowsize=0.75, fontname="Helvetica", fontsize=9];
  M [label="Generative models M"];
  E [label="Empirical model quotient\nModels / empirical equivalence"];
  R [label="Realizable reachable observation sets"];
  P [label="Observation invariant\nproperty or measurement"];
  M -> E [label="empirical class"];
  E -> R [label="canonical equivalence"];
  E -> P [label="unique descended map"];
  M -> P [label="invariant map F", style=dashed, constraint=false];
}
''',
    "concept_synthesis_dependency": r'''
digraph G {
  graph [rankdir=TB, bgcolor="transparent", pad="0.14", nodesep="0.34", ranksep="0.34", splines=polyline];
  node [shape=box, style="rounded,filled", fillcolor="white", color="#334155", fontname="Helvetica", fontsize=9.5, margin="0.13,0.08"];
  edge [color="#475569", penwidth=1.15, arrowsize=0.70];
  B [label="Boolean extension\nM* = M x {0,1}"];
  S [label="Strict latent cover\nM* -> M"];
  E [label="Same empirical class"];
  R [label="Same reachable\nobservation set"];
  O [label="Same outcome set\nfor admissible experiment e"];
  N [label="Noninjective extended\nobservation map"];
  D [label="No exact latent decoder"];
  T [label="Boundary limited observer\nsynthesis theorem", penwidth=1.8];
  B -> S;
  S -> E;
  S -> N;
  E -> R;
  E -> O;
  N -> D;
  {rank=same; R; O; D;}
  R -> T; O -> T; D -> T;
}
''',
}

for stem, dot in dots.items():
    dot_path = FIG / f"{stem}.dot"
    dot_path.write_text(dot, encoding="utf-8")
    for fmt in ("pdf", "svg"):
        subprocess.run(
            ["dot", f"-T{fmt}", str(dot_path), "-o", str(FIG / f"{stem}.{fmt}")],
            check=True,
        )

manifest: dict[str, object] = {
    "repository": "ezernackchristopher97-cloud/BoundaryObserver",
    "commit": "eb96b984ae999ee6cbc0aae33c2d501c46d9540f",
    "csv_files": {},
    "original_png_files": {},
    "vector_figures": sorted(p.name for p in FIG.glob("*.pdf")),
}

for p in sorted(DATA.glob("*.csv")):
    raw = p.read_bytes()
    manifest["csv_files"][p.name] = {
        "sha256": hashlib.sha256(raw).hexdigest(),
        "git_blob_sha": subprocess.check_output(
            ["git", "hash-object", str(p)], text=True
        ).strip(),
        "rows_excluding_header": max(
            0, sum(1 for _ in p.open(encoding="utf-8")) - 1
        ),
    }

for p in sorted((ROOT / "original_repo_pngs").glob("*.png")):
    raw = p.read_bytes()
    manifest["original_png_files"][p.name] = {
        "sha256": hashlib.sha256(raw).hexdigest(),
        "git_blob_sha": subprocess.check_output(
            ["git", "hash-object", str(p)], text=True
        ).strip(),
    }

(ROOT / "data_manifest.json").write_text(
    json.dumps(manifest, indent=2), encoding="utf-8"
)

print(
    json.dumps(
        {
            "pdf_figures": len(list(FIG.glob("*.pdf"))),
            "svg_figures": len(list(FIG.glob("*.svg"))),
        },
        indent=2,
    )
)

# Apply the readable layouts for the refinement and extension diagrams.
subprocess.run([__import__("sys").executable, str(ROOT / "draw_compact_diagrams.py")], check=True)
