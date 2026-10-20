# Sheaf.AlgebraicGeometry.CartesianChartExchangeRawNaturality

## Reason

The Sheaf module duplicates the retained source module
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeRawNaturality`. No live
module imports the Sheaf twin; the source `CartesianChartExchangeMapNaturality`
imports and uses the retained source twin. The retirement row in
`coord/retire-items.tsv` records this duplicate as a `SUPERSET` retirement.

## Old

The Sheaf module publicly imported
`WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality`
and declared the private helpers
`AlgebraicGeometry.Etale.rawRestrictedComparison_naturality_chosen` and
`AlgebraicGeometry.Etale.rawRestrictedComparison_naturality_chosen_at_x`.

## New

The Sheaf module is withdrawn and replaced by an empty module stub. The retained
source twin continues to provide the raw comparison naturality implementation.

## Users

| module | group holding it | effect |
|---|---|---|
| `WeilConjectures.AlgebraicGeometry.CartesianChartExchangeMapNaturality` | unclaimed | imports the retained `WeilConjectures` twin; no change required |

## Status

landed 20261020T221322-L-4173812 2026-10-20 (merge of deliver/R3/Sheaf.AlgebraicGeometry.CartesianChartExchangeRawNaturality)
