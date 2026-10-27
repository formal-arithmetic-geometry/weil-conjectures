# Coordinate adjunction proof interfaces

## Reason

The original Models theorem collects normalized ordinary tensor data, projection
adjunctions and finite chart compatibility in one hole. Separate these strict
parts while constructing the ordered iteration and étale chart adjunction in Lean.

## Old

No declarations existed in the four new modules. The original Models structure
and tower_coordinate_adjunction_models signature are preserved verbatim.

## New

Sheaf.Paper.SmoothPurityCoordinateFoundations defines Foundations (ordinary
normalizations, projective domains and chart preservation), its recursive
iteration, and coordinate_foundations.
Sheaf.Paper.SmoothPurityCoordinateProjectionModels defines ProjectionModels and
coordinate_projection_models for only ordered projections, including finite levels.
Sheaf.Paper.SmoothPurityCoordinateComposition defines restrictedIso, restrictedComposite and proves
restrictedComposite_counit from Mathlib composition and full inclusions.
Sheaf.Paper.SmoothPurityCoordinateChartModels explicitly constructs coordinateChartPair
and defines ChartModels and coordinate_chart_models for its finite compatibility
and independence of intermediate compactifications.

Each new structure has explicit data and no sorry. The only holes are whole named
public theorem proofs. No definition selects data from these existence theorems;
the original theorem destructs witnesses inside its proof only. The explicit chart
construction takes its normalized data and projection adjunctions as parameters.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | A7 | Same Models signature; proof assembles the three parts. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | new, A7 | Introduces proof interfaces and explicit iteration. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | new, A7 | Uses normalized foundation data. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | new, A7 | Generic categorical composition only. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | new, A7 | Uses foundations, projections and explicit restricted composition. |

Existing consumers see the same original structure, public imports and theorem.
No target signature or definition used by a target statement changes. New modules
are imported privately by the original item, so no consumer adaptation is required.

## Status

landed 20261025T161832-L-124555 2026-10-25 (merge of deliver/A7/Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels)
