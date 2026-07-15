# BoundaryObserver interface-refinement simulation report

## Scope

This report contains exhaustive calculations for four interfaces on one
eight-state finite world. It illustrates the refinement, strict-refinement,
and observable-quotient-map definitions in `BoundaryObserver.lean`. It is not
an additional proof and makes no claim beyond the formal framework.

## Interfaces

| Interface | Reachable observations | Quotient classes | Injective? |
| --- | --- | --- | --- |
| identity_interface | 8 | 8 | True |
| paired_bucket_interface | 4 | 4 | False |
| binary_region_interface | 2 | 2 | False |
| relabeled_identity_interface | 8 | 8 | True |

The identity and relabeled interfaces retain the same eight distinctions in
different observation representations. Paired buckets retain four classes,
and the binary region interface retains two.

## Refinements

| Refinement | Strict? | Collapsed pairs | Reverse exists? | Quotient map surjective? | Injective? |
| --- | --- | --- | --- | --- | --- |
| identity_to_paired | True | 4 | False | True | False |
| paired_to_region | True | 8 | False | True | False |
| identity_to_region | True | 12 | False | True | False |
| identity_to_relabeled | False | 0 | True | True | True |
| relabeled_to_identity | False | 0 | True | True | True |

For each listed relation, the explicit coarsening function satisfies the
observation-preservation equation on every enumerated world state. The three
strict rows contain a calculated collapsed pair and have noninjective induced
quotient maps. The two relabeling rows have the same observational resolution
and bijective quotient maps.

## Detailed finite records

- `quotient_maps.csv` contains 36 class-map entries.
- `collapsed_pairs.csv` contains 24 strict-collapse records.
- `interface_summary.csv` and `refinement_summary.csv` contain the aggregate
  calculations used above.

## Generated plots

- `observable_quotient_size_by_interface.png`
- `collapsed_pairs_by_refinement.png`
