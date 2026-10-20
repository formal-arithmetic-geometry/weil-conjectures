# AlgebraicGeometry.Etale.geometricPointSectionsImageH0Iso

## Reason

Factor the existing formula through a generic comparison definition in the same module.
The generic definitions have precisely the original bodies, so the replacement is
definitionally equal. This avoids repeated kernel checking of the composite expression
at concrete sheaf categories. All signatures and all mathematical objects stay identical.
No target changes, even up to propositional equality.

## Old

```lean
noncomputable def geometricPointSectionsImageH0Iso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
          (geometricPointStalk Ω).mapDerivedCategory).obj
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (geometricPointStalk Ω).obj ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) :=
  ((geometricPointStalk Ω).mapDerivedCategoryHomologyFunctorIso 0).symm.app _ ≪≫
    (geometricPointStalk Ω).mapIso
      ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h
        |>.homologyRightDerivedFunctorObjSingleFunctorIso G 0) ≪≫
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedZeroIsoSelf.app G)
```

## New

```lean
noncomputable def geometricPointSectionsImageH0Iso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
          (geometricPointStalk Ω).mapDerivedCategory).obj
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (geometricPointStalk Ω).obj ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) :=
  Functor.geometricSectionsExactSingleH0Iso
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h) (geometricPointStalk Ω) G
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | P5 | Same definitionally equal comparison; main theorem unchanged. |

No consumer needs adaptation because the replacement is definitionally equal.

## Status

landed 20261020T132020-L-1402192 2026-10-20 (merge of deliver/P5/Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction)
