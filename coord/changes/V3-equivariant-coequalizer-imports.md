# Sheaf.CategoryTheory.EquivariantCoequalizerComparison public imports

## Reason

The theorem concerns arbitrary internal modules in a monoidal category. Mathlib's
`Monoidal.Mod` supplies the module category, its forgetful functor, and the self-action
of a monoidal category. No ring presheaf or sheaf construction is used. Remove the
unnecessary public import of `RingPresheaf`. Every declaration signature is unchanged.

## Old

```lean
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
```

## New

```lean
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Monoidal.Mod
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.EquivariantCoequalizerComparison | V3 | Proved with generic Mathlib imports. |

There are no existing Lean importers. The unfinished DAG parents still need this
comparison; its Lean attachment, statement dependencies and proof dependencies are
preserved. No consumer adaptation and no target statement change is required.

## Status

landed 20261021T120812-L-3949737 2026-10-21 (merge of deliver/V3/Sheaf.CategoryTheory.EquivariantCoequalizerComparison)
