# SmoothLocalAcyclicity core import

## Reason
The item's proof imports the newly split core theorem to assemble universal local acyclicity.

## Old
The item had no proof-only import of `Sheaf.AlgebraicGeometry.SmoothLocalAcyclicityCore`.

## New
The item imports `Sheaf.AlgebraicGeometry.SmoothLocalAcyclicityCore` and applies
`smooth_localAcyclicity_core` to `pullback.snd f g` and to `f`.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.SmoothLocalAcyclicity | Z9 | proof uses the split core theorem |

## Status
landed 20261018T071246-L-1684332 2026-10-18 (merge of deliver/Z9/Sheaf.AlgebraicGeometry.SmoothLocalAcyclicity)
