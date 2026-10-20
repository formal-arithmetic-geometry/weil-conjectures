# Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases imports

## Reason

`Mathlib.LinearAlgebra.ExteriorPower.Basis` is not referenced by the module's
statement or proof. Removing the public import keeps the module compiling and
avoids exporting an unnecessary dependency.

## Old

```lean
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
```

## New

The import line is removed. The module continues to import every dependency
needed by its public statement and proof.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.KoszulSelfExtExterior | unclaimed | Its direct imports remain sufficient; no adaptation needed. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal | unclaimed | Its direct imports remain sufficient; no adaptation needed. |

## Status

landed 20261020T174840-L-808924 2026-10-20 (merge of deliver/R5/Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases)
