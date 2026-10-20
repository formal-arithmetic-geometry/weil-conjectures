# AlgebraicGeometry.Etale.geometricPointSectionsImageAdjunction

## Reason

Construct the canonical derived adjunction directly from the exact left adjoint and the
right-derived unit. This avoids expanding the left-derived flat-resolution construction
and its subsequent exact-functor transport during concrete geometric calculations.
The private theorem `canonicalDerivedAdjunction_eq` proves equality of these two
adjunction constructions from their defining unit equations. The functors, unit, counit
and all declaration signatures are therefore unchanged mathematically. Targets using this
definition should be reviewed with this equality in mind; no target text changes.

## Old

```lean
noncomputable def geometricPointSectionsImageAdjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory ⊣
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).ofNatIsoLeft
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).leftDerivedFunctorIsoMapDerivedCategory
```

## New

```lean
noncomputable def geometricPointSectionsImageAdjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory ⊣
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor :=
  (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategoryRightDerivedAdjunction
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | P5 | Its three original uses retain the same adjunction; private comparison proofs now use reflexivity. |

`tools/downstream.py --uses geometricPointSectionsImageAdjunction` finds no direct user outside this module.
Its thirteen transitive importers require no adaptation because every signature stays identical.

## Status

landed 20261020T132020-L-1402192 2026-10-20 (merge of deliver/P5/Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction)
