# GlobalHomAdjunctionIso proof helper interface

## Reason

Stage-3 proof helpers are declared in the item module so the long mate and Leray calculations can be elaborated with explicit category variables and fixed monoidal instances. The static delivery checker sees these `variable` commands as interface changes.

## Old

The module's universe declaration was:

```lean
universe u w
```

The generic helper sections and the scoped omission of the global ModuleCat derived
instance did not exist. Every public definition and theorem signature is unchanged.

## New

The module's universe declaration is:

```lean
universe u w vC vD vE vB uC uD uE uB
```

The item module declares private generic category variables and private helper theorems/definitions for the evaluation mate, tensor-Hom adjunction construction and Leray naturality. These declarations are private and cannot be referenced by importing modules; the commands only stabilize elaboration of the item proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso | R3 | proof elaboration only; no public theorem signature changes |

## Status

landed 20261012T135310-L-1689664 2026-10-12 (merge of deliver/R3/Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso)
