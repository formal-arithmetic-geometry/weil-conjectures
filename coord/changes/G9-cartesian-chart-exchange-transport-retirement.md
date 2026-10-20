# CartesianChartExchangeTransport duplicate retirement

## Reason

This is the listed retirement item in coord/retire-items.tsv, authorized by the
human hand-off in coord/changes/retire-sheaf-twins-20261020.md. The Sheaf module has
zero holes and eight private lemmas. All eight signatures and complete proofs
agree with the upstream twin after ignoring comments and whitespace. The two
consumers can use the upstream proofs directly. The upstream source is untouched.

## Old

The direct consumers privately import the duplicate:

```lean
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport
```

The duplicate declares add_iso_trans_apply, yoneda_mapIso_apply,
coyoneda_mapIso_apply, chartAdjunct_as_actual, chartCoefficient_hom,
chart_inv_diagonal, chart_inv_leg and chartAdjunct_pullback, all private.

## New

The two consumers privately import the existing upstream implementation:

```lean
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeTransport
```

The duplicate is withdrawn through deleted.txt. Each consumer changes exactly
one import line. Every declaration, proof, public import and signature in the
consumers is preserved. No definition or target statement changes.

No DAG node or unit references this copy, and no quarantined Lean source
references it. There is consequently no node attachment or parent dependency
to migrate, and no unit route changes. The five consumer import closures
introduce no new Sheaf/WeilConjectures twin pairs. The Lift consumers lose the
Transport pair; their pre-existing Comparison and Evaluation pairs remain.
The direct consumers have no twin pairs before or after migration.

## Users

All five transitive importers from tools/downstream.py are listed, together with
the retired item. Neither adapted consumer has a claim in the coordination
snapshot. Both adapted consumers compile cleanly against the migrated imports,
as does the unchanged LiftCoherence. The two other transitive consumers hit the
60-second limit against both the overlay and the original baseline; this
pre-existing validation limitation is recorded in report.md. Unchanged
validation copies are excluded from the delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport | G9 | Withdraw duplicate; retain upstream implementation. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation | unclaimed | Migrate private proof import; declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison | unclaimed | Migrate private proof import; declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence | unclaimed | No source change; validate against migrated consumers. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftRawNaturality | unclaimed | No source change; validate against migrated consumers. |
| Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality | unclaimed | No source change; validate against migrated consumers. |

## Status

landed 20261020T230747-L-609763 2026-10-20 (merge of deliver/G9/Sheaf.AlgebraicGeometry.CartesianChartExchangeTransport)
