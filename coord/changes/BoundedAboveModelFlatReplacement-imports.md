# BoundedAboveModelFlatReplacement imports

## Reason

The proof does not use `StandardSingleFlatCounitPresentation`. The module's
statement requires `DerivedCategory` and `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`,
while `BoundedFlatReplacement` is proof-only and should be private.

## Old

```lean
public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import Sheaf.Algebra.Homology.BoundedFlatReplacement
```

## New

```lean
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.BoundedFlatReplacement
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionCore | unclaimed | Its own public import of `StandardSingleFlatCounitPresentation` supplies the presentation declarations; no proof or statement change is required. |

## Status

landed 20261014T010840-L-3162852 2026-10-14 (merge of deliver/G1/Sheaf.AlgebraicGeometry.BoundedAboveModelFlatReplacement)
