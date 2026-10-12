# AlgebraicGeometry.RingedSpace.moduleGrothendieckAbelian

## Reason

The existing source library proves the required Grothendieck structure directly.
The former proof used the first conjunct of a stronger unfinished resolution theorem.
Replace this proof and remove the unused public import
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`; add the source theorem as a
proof-only import. No declaration signature or mathematical definition changes.
The direct import of `Mathlib.Algebra.Homology.DerivedCategory.KInjective` is also
made proof-only: its types are already publicly available through
`RightDerivedFunctor.Defs`, and its quasi-isomorphism criterion is used in a proof.
The instance is proposition-valued, so its new proof is equal to its old proof by
proof irrelevance. Target statements and their meanings are unchanged.

## Old

```lean
instance moduleGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X)) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
    (Opens.grothendieckTopology X) X.sheaf).1
```

## New

```lean
instance moduleGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X)) :=
  SheafOfModules.isGrothendieckAbelian (moduleRings X)
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage --uses
AlgebraicGeometry.RingedSpace.moduleGrothendieckAbelian` reports no textual users.
Existing users of derived direct image see the same types and instances; no adaptation
is required. The removed import supplies no names needed by the remaining declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage | P1 | Same instance proposition; proved source-library implementation and pruned import. |

## Status

landed 20261012T095916-L-321942 2026-10-12 (merge of deliver/P1/Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage)
