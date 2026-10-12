# AlgebraicGeometry.Proj.gradedModuleChart_basisComparison

## Reason
The proof now delegates to a fixed-chart intermediate theorem; the elaborated statement is unchanged.

## Old
The theorem was proved with `sorry`.

## New
The theorem applies `gradedModuleChart_basisComparison_fixed` for each chart.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProjGradedModuleChartTildeComparison | unclaimed | proof dependency remains available; no interface change |

## Status
landed 20261012T184313-L-4007901 2026-10-12 (merge of deliver/K1/Sheaf.AlgebraicGeometry.ProjGradedModuleChartBasisComparison)
