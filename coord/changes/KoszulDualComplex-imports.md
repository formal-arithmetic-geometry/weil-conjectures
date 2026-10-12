# Sheaf.RingTheory.KoszulDualComplex imports

## Reason

`Mathlib.CategoryTheory.Linear.Yoneda` is not used by any declaration or proof in the module.
Removing it prunes an unnecessary public dependency while preserving all exported declarations.

## Old

```lean
public import Mathlib.CategoryTheory.Linear.Yoneda
```

## New

The import is removed. The remaining imports are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.KoszulConormalComparison | unclaimed | Compiles unchanged; it uses the Koszul dual declarations only. |

## Status

landed 20261012T194120-L-458114 2026-10-12 (merge of deliver/K1/Sheaf.RingTheory.KoszulDualComplex)
