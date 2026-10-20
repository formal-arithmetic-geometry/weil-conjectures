# AlgebraicGeometry.ProEtale.projectiveLineTraceComponents

## Reason

The target proof is decomposed into two independently named component theorems. This
adds public theorem declarations that a future proof consumer can import directly.

## Old

The item module exposed only the original target theorem and its existing definitions.

## New

The item module also exposes `exists_spP1BaseTraceConditions` and
`spP1DiagonalIntegrals_of_twisted`, each with a DAG node and a named proof obligation.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace | B4 | The target theorem combines the two component results. |

## Status

landed 20261020T230718-L-604300 2026-10-20 (merge of deliver/B4/Sheaf.AlgebraicGeometry.ProEtaleProjectiveLineTrace)
