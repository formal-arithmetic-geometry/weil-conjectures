# AlgebraicGeometry.Etale.geometricPointSectionsGlobalH0Iso

## Reason

Factor the existing formula through a generic comparison definition in the same module.
The generic definitions have precisely the original bodies, so the replacement is
definitionally equal. This avoids repeated kernel checking of the composite expression
at concrete sheaf categories. All signatures and all mathematical objects stay identical.
No target changes, even up to propositional equality.

## Old

```lean
noncomputable def geometricPointSectionsGlobalH0Iso (Z : Scheme.{u})
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G :=
  (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    |>.homologyRightDerivedFunctorObjSingleFunctorIso G 0) ≪≫
    (Sheaf.Γ Z.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).rightDerivedZeroIsoSelf.app G
```

## New

```lean
noncomputable def geometricPointSectionsGlobalH0Iso (Z : Scheme.{u})
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G :=
  Functor.geometricSectionsSingleH0Iso
    (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) G
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction | P5 | Same definitionally equal comparison; main theorem unchanged. |

No consumer needs adaptation because the replacement is definitionally equal.

## Status

landed 20261020T132020-L-1402192 2026-10-20 (merge of deliver/P5/Sheaf.AlgebraicGeometry.GeometricPointDerivedSectionsAdjunction)
