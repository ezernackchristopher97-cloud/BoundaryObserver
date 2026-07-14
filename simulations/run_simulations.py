#!/usr/bin/env python3
"""Run every finite BoundaryObserver simulation and write reproducible outputs."""

from __future__ import annotations

import argparse
import csv
from pathlib import Path
from typing import Iterable

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

try:  # Support both ``python simulations/run_simulations.py`` and ``python -m``.
    from .boundary_observer.analysis import (
        collapsed_pair_rows,
        compare_experiment_outcomes,
        empirical_quotient_rows,
        interface_summary_rows,
        nonidentifiable_property_rows,
        observation_fiber_rows,
        predicate_profile_rows,
        quotient_map_rows,
        refinement_summary_rows,
        summarize_multiplicities,
    )
    from .boundary_observer.experiments import (
        ObservationPredicate,
        categorical_partition_experiment,
        compressed_numerical_experiment,
        identity_experiment,
        threshold_experiment,
    )
    from .boundary_observer.models import (
        GenerativeModel,
        boolean_hidden_extension,
        make_base_model,
    )
    from .boundary_observer.interfaces import standard_refinement_family
except ImportError:
    from boundary_observer.analysis import (
        collapsed_pair_rows,
        compare_experiment_outcomes,
        empirical_quotient_rows,
        interface_summary_rows,
        nonidentifiable_property_rows,
        observation_fiber_rows,
        predicate_profile_rows,
        quotient_map_rows,
        refinement_summary_rows,
        summarize_multiplicities,
    )
    from boundary_observer.experiments import (
        ObservationPredicate,
        categorical_partition_experiment,
        compressed_numerical_experiment,
        identity_experiment,
        threshold_experiment,
    )
    from boundary_observer.models import (
        GenerativeModel,
        boolean_hidden_extension,
        make_base_model,
    )
    from boundary_observer.interfaces import standard_refinement_family


SIMULATIONS_DIR = Path(__file__).resolve().parent
DEFAULT_RESULTS_DIR = SIMULATIONS_DIR / "results"


def write_csv(path: Path, rows: list[dict[str, object]]) -> None:
    if not rows:
        raise ValueError(f"refusing to write an empty summary: {path}")
    fieldnames = list(rows[0])
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(
            handle, fieldnames=fieldnames, lineterminator="\n"
        )
        writer.writeheader()
        writer.writerows(rows)


def _plot_metric(
    rows: list[dict[str, object]],
    metric: str,
    ylabel: str,
    title: str,
    path: Path,
) -> None:
    multiplicities = [int(row["hidden_multiplicity"]) for row in rows]
    values = [float(row[metric]) for row in rows]
    figure, axis = plt.subplots(figsize=(7.2, 4.6))
    axis.plot(multiplicities, values, marker="o", linewidth=2)
    axis.set_xlabel("Hidden multiplicity")
    axis.set_ylabel(ylabel)
    axis.set_title(title)
    axis.set_xticks(multiplicities)
    axis.grid(alpha=0.3)
    figure.tight_layout()
    figure.savefig(path, dpi=160)
    plt.close(figure)


def _plot_experiment_outcomes(
    rows: list[dict[str, object]],
    experiments: Iterable[object],
    models: Iterable[GenerativeModel],
    path: Path,
) -> None:
    model_names = {model.name for model in models}
    figure, axis = plt.subplots(figsize=(7.2, 4.6))
    styles = (
        {"marker": "o", "linewidth": 2.2, "linestyle": "-"},
        {"marker": "s", "linewidth": 2.2, "linestyle": "--"},
        {"marker": "^", "linewidth": 5.0, "linestyle": "-"},
        {"marker": "D", "linewidth": 2.0, "linestyle": ":"},
    )
    for experiment, style in zip(experiments, styles, strict=False):
        selected = sorted(
            (
                row
                for row in rows
                if row["experiment"] == experiment.name
                and row["model"] in model_names
            ),
            key=lambda row: int(row["hidden_multiplicity"]),
        )
        axis.plot(
            [int(row["hidden_multiplicity"]) for row in selected],
            [int(row["outcome_count"]) for row in selected],
            label=experiment.name,
            **style,
        )
    multiplicities = sorted(
        {model.hidden_multiplicity for model in models}
    )
    axis.set_xlabel("Hidden multiplicity")
    axis.set_ylabel("Possible experiment outcome count")
    axis.set_title("Observation-only outcomes remain fixed")
    axis.set_xticks(multiplicities)
    axis.grid(alpha=0.3)
    axis.legend(fontsize=8)
    figure.tight_layout()
    figure.savefig(path, dpi=160)
    plt.close(figure)


def _plot_interface_quotient_sizes(
    rows: list[dict[str, object]], path: Path
) -> None:
    labels = [str(row["interface"]).replace("_interface", "") for row in rows]
    sizes = [int(row["observable_quotient_size"]) for row in rows]
    figure, axis = plt.subplots(figsize=(8.0, 4.8))
    bars = axis.bar(labels, sizes, color=("#2563eb", "#7c3aed", "#db2777", "#0891b2"))
    axis.bar_label(bars, padding=3)
    axis.set_ylabel("Observable quotient class count")
    axis.set_title("Finite interfaces retain different numbers of distinctions")
    axis.set_ylim(0, max(sizes) + 1.5)
    axis.grid(axis="y", alpha=0.25)
    axis.tick_params(axis="x", rotation=15)
    figure.tight_layout()
    figure.savefig(path, dpi=160)
    plt.close(figure)


def _plot_collapsed_pairs(
    rows: list[dict[str, object]], path: Path
) -> None:
    labels = [str(row["refinement"]).replace("_to_", " → ") for row in rows]
    counts = [int(row["collapsed_world_pair_count"]) for row in rows]
    figure, axis = plt.subplots(figsize=(8.0, 4.8))
    bars = axis.barh(labels, counts, color="#c2410c")
    axis.bar_label(bars, padding=3)
    axis.set_xlabel("Pairs distinguished by fine and identified by coarse")
    axis.set_title("Collapsed pairs under finite coarsening")
    axis.set_xlim(0, max(counts) + 2)
    axis.grid(axis="x", alpha=0.25)
    figure.tight_layout()
    figure.savefig(path, dpi=160)
    plt.close(figure)


def _markdown_table(headers: list[str], rows: list[list[object]]) -> str:
    lines = [
        "| " + " | ".join(headers) + " |",
        "| " + " | ".join("---" for _ in headers) + " |",
    ]
    lines.extend(
        "| " + " | ".join(str(value) for value in row) + " |" for row in rows
    )
    return "\n".join(lines)


def _write_report(
    path: Path,
    base: GenerativeModel,
    noninjective_base: GenerativeModel,
    boolean_extension: GenerativeModel,
    multiplicity_rows: list[dict[str, object]],
    experiment_rows: list[dict[str, object]],
    predicate_rows: list[dict[str, object]],
    quotient_rows: list[dict[str, object]],
    property_rows: list[dict[str, object]],
) -> None:
    boolean_checks = [
        (
            "Same reachable observations",
            base.reachable_observations
            == boolean_extension.reachable_observations,
        ),
        (
            "Twice as many latent states",
            boolean_extension.latent_state_count == 2 * base.latent_state_count,
        ),
        ("Contains a latent collision", boolean_extension.latent_collision_count > 0),
        (
            "Globally exact latent decoder is impossible",
            not boolean_extension.exact_latent_decoder_possible,
        ),
        (
            "Same empirical equivalence class",
            base.is_empirically_equivalent_to(boolean_extension),
        ),
    ]
    multiplicity_table = _markdown_table(
        [
            "Multiplicity",
            "Latent states",
            "Reachable observations",
            "Average fiber",
            "Maximum fiber",
            "Collisions",
            "Exact decoder?",
        ],
        [
            [
                row["hidden_multiplicity"],
                row["latent_state_count"],
                row["reachable_observation_count"],
                f"{float(row['average_fiber_size']):.2f}",
                row["maximum_fiber_size"],
                row["latent_collision_count"],
                row["exact_latent_decoder_possible"],
            ]
            for row in multiplicity_rows
        ],
    )
    experiment_summary = []
    for experiment_name in dict.fromkeys(
        str(row["experiment"]) for row in experiment_rows
    ):
        rows = [
            row for row in experiment_rows if row["experiment"] == experiment_name
        ]
        experiment_summary.append(
            [
                experiment_name,
                rows[0]["possible_outcomes"],
                all(bool(row["matches_base_outcomes"]) for row in rows),
            ]
        )
    quotient_table = _markdown_table(
        ["Class", "Canonical reachable set", "Latent cardinalities", "Models"],
        [
            [
                row["empirical_class"],
                row["canonical_reachable_observations"],
                row["latent_cardinalities"],
                row["model_names"],
            ]
            for row in quotient_rows
        ],
    )
    property_table = _markdown_table(
        ["Latent property", "Base", "Boolean extension", "Varies"],
        [
            [
                row["property"],
                row["base_value"],
                row["extension_value"],
                row["varies_within_empirical_class"],
            ]
            for row in property_rows
        ],
    )

    report = f"""# BoundaryObserver simulation report

## Scope

These are exhaustive calculations for explicitly enumerated finite examples.
They illustrate selected structures proved in `BoundaryObserver.lean`; they are
not additional mathematical proofs and are not empirical confirmation of any
metaphysical claim.

## Base examples

- `{base.name}` has {base.latent_state_count} latent states, reachable set
  `{sorted(base.reachable_observations)}`, and an injective observation map.
- `{noninjective_base.name}` has {noninjective_base.latent_state_count} latent
  states, reachable set `{sorted(noninjective_base.reachable_observations)}`,
  and a noninjective observation map.

## Boolean hidden extension

{_markdown_table(["Check", "Calculated result"], [[name, result] for name, result in boolean_checks])}

## Finite hidden multiplicities

{multiplicity_table}

In this run the reachable observation set is unchanged for every listed
multiplicity.  Fiber and collision values are calculations for these models.

## Admissible experiment outcomes

{_markdown_table(["Experiment", "Base possible outcomes", "All listed models match"], experiment_summary)}

Each experiment is a function of accessible observations only.

## Predicate profiles

All {len(predicate_rows)} model/predicate profile comparisons match the base:
`{all(bool(row['matches_base_profile']) for row in predicate_rows)}`.
The full truth profiles are stored in `predicate_profiles.csv`.

## Finite empirical quotient

{quotient_table}

Class membership above is computed solely by equality of reachable observation
sets.  The canonical class label is the sorted representation of that set.

## Latent properties not fixed by this empirical class

{property_table}

For this base/extension pair, reachable observations and all tested admissible
experiment outcome sets agree while the displayed latent properties vary.
This is a finite witness within the framework, not a claim beyond it.

## Generated plots

- `latent_state_count_vs_hidden_multiplicity.png`
- `reachable_observation_count_vs_hidden_multiplicity.png`
- `maximum_fiber_size_vs_hidden_multiplicity.png`
- `experiment_outcome_count_vs_hidden_multiplicity.png`
"""
    path.write_text(report, encoding="utf-8")


def _write_refinement_report(
    path: Path,
    interface_rows: list[dict[str, object]],
    refinement_rows: list[dict[str, object]],
    quotient_rows: list[dict[str, object]],
    collapsed_rows: list[dict[str, object]],
) -> None:
    interface_table = _markdown_table(
        ["Interface", "Reachable observations", "Quotient classes", "Injective?"],
        [
            [
                row["interface"],
                row["reachable_observation_count"],
                row["observable_quotient_size"],
                row["observation_function_injective"],
            ]
            for row in interface_rows
        ],
    )
    refinement_table = _markdown_table(
        [
            "Refinement",
            "Strict?",
            "Collapsed pairs",
            "Reverse exists?",
            "Quotient map surjective?",
            "Injective?",
        ],
        [
            [
                row["refinement"],
                row["strict_refinement"],
                row["collapsed_world_pair_count"],
                row["reverse_refinement_exists"],
                row["quotient_map_surjective"],
                row["quotient_map_injective"],
            ]
            for row in refinement_rows
        ],
    )
    report = f"""# BoundaryObserver interface-refinement simulation report

## Scope

This report contains exhaustive calculations for four interfaces on one
eight-state finite world. It illustrates the refinement, strict-refinement,
and observable-quotient-map definitions in `BoundaryObserver.lean`. It is not
an additional proof and makes no claim beyond the formal framework.

## Interfaces

{interface_table}

The identity and relabeled interfaces retain the same eight distinctions in
different observation representations. Paired buckets retain four classes,
and the binary region interface retains two.

## Refinements

{refinement_table}

For each listed relation, the explicit coarsening function satisfies the
observation-preservation equation on every enumerated world state. The three
strict rows contain a calculated collapsed pair and have noninjective induced
quotient maps. The two relabeling rows have the same observational resolution
and bijective quotient maps.

## Detailed finite records

- `quotient_maps.csv` contains {len(quotient_rows)} class-map entries.
- `collapsed_pairs.csv` contains {len(collapsed_rows)} strict-collapse records.
- `interface_summary.csv` and `refinement_summary.csv` contain the aggregate
  calculations used above.

## Generated plots

- `observable_quotient_size_by_interface.png`
- `collapsed_pairs_by_refinement.png`
"""
    path.write_text(report, encoding="utf-8")


def run(output_dir: Path) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)

    base = make_base_model(6, injective=True, name="injective_base")
    noninjective_base = make_base_model(
        6,
        injective=False,
        observation_count=3,
        name="noninjective_base",
    )
    boolean_extension = boolean_hidden_extension(
        base, name="boolean_hidden_extension"
    )
    multiplicities = (1, 2, 3, 5, 8)
    multiplicity_rows, multiplicity_models = summarize_multiplicities(
        base, multiplicities
    )

    experiments = (
        identity_experiment(),
        threshold_experiment(3),
        categorical_partition_experiment(
            {"low": (0, 1), "middle": (2, 3), "high": (4, 5)}
        ),
        compressed_numerical_experiment(2),
    )
    compared_models = [base, boolean_extension, *multiplicity_models]
    experiment_rows = compare_experiment_outcomes(
        base, compared_models, experiments
    )

    predicates = (
        ObservationPredicate("is_even", lambda observation: observation % 2 == 0),
        ObservationPredicate("at_least_three", lambda observation: observation >= 3),
        ObservationPredicate(
            "is_endpoint", lambda observation: observation in {0, 5}
        ),
    )
    predicate_rows = predicate_profile_rows(
        base, compared_models, predicates
    )
    quotient_rows = empirical_quotient_rows(
        [base, noninjective_base, boolean_extension, *multiplicity_models]
    )
    property_rows = nonidentifiable_property_rows(
        base, boolean_extension, experiments
    )
    model_rows = [
        model.summary()
        for model in [
            base,
            noninjective_base,
            boolean_extension,
            *multiplicity_models,
        ]
    ]
    fiber_rows = observation_fiber_rows(
        [base, noninjective_base, boolean_extension, *multiplicity_models]
    )
    interfaces, refinements = standard_refinement_family()
    interface_rows = interface_summary_rows(interfaces)
    refinement_rows = refinement_summary_rows(refinements)
    interface_quotient_rows = quotient_map_rows(refinements)
    interface_collapsed_rows = collapsed_pair_rows(refinements)

    # Fail loudly if a construction no longer satisfies its intended finite checks.
    assert base.reachable_observations == boolean_extension.reachable_observations
    assert boolean_extension.latent_state_count == 2 * base.latent_state_count
    assert not boolean_extension.is_injective
    assert not boolean_extension.exact_latent_decoder_possible
    assert all(
        bool(row["empirically_equivalent_to_base"])
        for row in multiplicity_rows
    )
    assert all(bool(row["matches_base_outcomes"]) for row in experiment_rows)
    assert all(bool(row["matches_base_profile"]) for row in predicate_rows)
    assert all(bool(row["varies_within_empirical_class"]) for row in property_rows)
    assert all(bool(row["observation_preserved"]) for row in refinement_rows)
    assert all(
        bool(row["fine_obs_equivalence_implies_coarse"])
        for row in refinement_rows
    )
    assert all(bool(row["quotient_map_surjective"]) for row in refinement_rows)
    assert all(
        not bool(row["quotient_map_injective"])
        and not bool(row["reverse_refinement_exists"])
        for row in refinement_rows
        if bool(row["strict_refinement"])
    )
    assert all(
        bool(row["quotient_map_bijective"])
        and bool(row["same_observational_resolution"])
        for row in refinement_rows
        if not bool(row["strict_refinement"])
    )

    write_csv(output_dir / "model_summary.csv", model_rows)
    write_csv(output_dir / "multiplicity_summary.csv", multiplicity_rows)
    write_csv(output_dir / "experiment_outcomes.csv", experiment_rows)
    write_csv(output_dir / "predicate_profiles.csv", predicate_rows)
    write_csv(output_dir / "empirical_quotient.csv", quotient_rows)
    write_csv(output_dir / "nonidentifiable_properties.csv", property_rows)
    write_csv(output_dir / "observation_fibers.csv", fiber_rows)
    write_csv(output_dir / "interface_summary.csv", interface_rows)
    write_csv(output_dir / "refinement_summary.csv", refinement_rows)
    write_csv(output_dir / "quotient_maps.csv", interface_quotient_rows)
    write_csv(output_dir / "collapsed_pairs.csv", interface_collapsed_rows)

    _plot_metric(
        multiplicity_rows,
        "latent_state_count",
        "Latent state count",
        "Latent states grow with hidden multiplicity",
        output_dir / "latent_state_count_vs_hidden_multiplicity.png",
    )
    _plot_metric(
        multiplicity_rows,
        "reachable_observation_count",
        "Reachable observation count",
        "Reachable observations remain fixed",
        output_dir / "reachable_observation_count_vs_hidden_multiplicity.png",
    )
    _plot_metric(
        multiplicity_rows,
        "maximum_fiber_size",
        "Maximum fiber size",
        "Maximum fiber size grows with hidden multiplicity",
        output_dir / "maximum_fiber_size_vs_hidden_multiplicity.png",
    )
    _plot_experiment_outcomes(
        experiment_rows,
        experiments,
        multiplicity_models,
        output_dir / "experiment_outcome_count_vs_hidden_multiplicity.png",
    )
    _plot_interface_quotient_sizes(
        interface_rows,
        output_dir / "observable_quotient_size_by_interface.png",
    )
    _plot_collapsed_pairs(
        refinement_rows,
        output_dir / "collapsed_pairs_by_refinement.png",
    )
    _write_report(
        output_dir / "report.md",
        base,
        noninjective_base,
        boolean_extension,
        multiplicity_rows,
        experiment_rows,
        predicate_rows,
        quotient_rows,
        property_rows,
    )
    _write_refinement_report(
        output_dir / "refinement_report.md",
        interface_rows,
        refinement_rows,
        interface_quotient_rows,
        interface_collapsed_rows,
    )

    print(f"Simulation outputs written to {output_dir}")
    print(
        "Verified Boolean, multiplicity, experiment, predicate, quotient, "
        "and interface-refinement checks."
    )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_RESULTS_DIR,
        help=f"output directory (default: {DEFAULT_RESULTS_DIR})",
    )
    return parser.parse_args()


if __name__ == "__main__":
    arguments = parse_args()
    run(arguments.output_dir.resolve())
