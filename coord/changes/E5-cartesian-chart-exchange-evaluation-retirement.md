# Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation

## Reason

Retire the assigned duplicate in `coord/retire-items.tsv`. The upstream
`WeilConjectures.AlgebraicGeometry.CartesianChartExchangeEvaluation` supplies the
same private `cartesianChartAdjunct_spec` and `chartCohomologyIso_eval`
declarations used by the remaining consumer. The Sheaf copy is therefore
unneeded after its proof import is migrated.

## Old

`Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison` privately imported:

```lean
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation
```

The duplicate module declared the two private chart evaluation theorems (and
private proof helpers used only by them).

## New

The consumer privately imports:

```lean
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeEvaluation
```

The duplicate module is withdrawn through `deleted.txt`. The DAG attachment for
`lem-sc-cartesian-chart-cohomology-evaluation` now records the upstream
`WeilConjectures` declaration. No source module, public signature, target
statement, or unit route changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation | E5 | Withdraw duplicate; upstream twin retained. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison | unclaimed | Change one proof import to the upstream twin. |
| Sheaf.AlgebraicGeometry.CartesianChartRestrictedMapEvaluation | unclaimed | Already withdrawn; no adaptation remains. |

## Status

landed 20261020T233122-L-896269 2026-10-20 (merge of deliver/E5/Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation)
