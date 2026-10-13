# singleComplexOpenComparison_union_ses_objects proof commands

## Reason

The proof adds a local `dsimp` and `let` command context required to apply the core
chain-model theorem. This affects elaboration visibility only and preserves the theorem
signature.

## Old

The theorem body was `by sorry`.

## New

The theorem body uses `dsimp only`, local `let a`, and applications of the core and generic
mapping-cylinder theorems.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESPresentation | unclaimed | proof sees the same target signature |

## Status

landed 20261013T231544-L-1820751 2026-10-13 (merge of deliver/S2/Sheaf.AlgebraicGeometry.SingleComplexOpenUnionSESObjects)
