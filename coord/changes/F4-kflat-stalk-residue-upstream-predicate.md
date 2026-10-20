# AlgebraicGeometry.Scheme.nonempty_kFlat_stalk_residueCohomology_linearEquiv

## Reason

Restore the quarantined module from its archive. The 2026-10-20 upstream sync renamed
`CochainComplex.IsAcyclicTensorKFlat` to `CochainComplex.IsKFlatTensor`.
The archived hypothesis no longer elaborates. Both predicates say that total tensoring
with the complex takes every acyclic sheaf complex to an acyclic complex; this is an
API rename, with no change to the mathematical statement. The current
`derivedPullback_spec` consumes exactly `IsKFlatTensor`.

## Old

```lean
theorem nonempty_kFlat_stalk_residueCohomology_linearEquiv
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := X.sheaf) P)
    (eP : DerivedCategory.Q.obj P ≅ E) (i : ℤ) :
    Nonempty (derivedFiberCohomology X E i x ≃ₗ[IsLocalRing.ResidueField
      (X.presheaf.stalk x)]
        ((((ModuleCat.extendScalars
          (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)).homology i))
```

## New

```lean
theorem nonempty_kFlat_stalk_residueCohomology_linearEquiv
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (eP : DerivedCategory.Q.obj P ≅ E) (i : ℤ) :
    Nonempty (derivedFiberCohomology X E i x ≃ₗ[IsLocalRing.ResidueField
      (X.presheaf.stalk x)]
        ((((ModuleCat.extendScalars
          (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
              (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)).homology i))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology | F4 | Restored with the current predicate; existing complete proof compiles. |
| Sheaf.AlgebraicGeometry.StalkFreeResidueCohomologyComparison | unclaimed (quarantined) | Its call passes hP from exists_isKFlatResolution, which now has the required IsKFlatTensor type. No call-site edit needed. |
| Sheaf.AlgebraicGeometry.DerivedFiberCohomologyBaseChange | unclaimed (quarantined) | Calls retain identical arguments and conclusion. Its explicit hPg annotation separately uses the obsolete predicate name and already fails against current upstream; this pre-existing quarantine repair is independent of restoring the present module. |
| Sheaf.AlgebraicGeometry.ResidueBettiZeroOfTensorVanishing | unclaimed (quarantined) | Call and conclusion unchanged; hP is a K-flat representative. Its public dependency DerivedTensorCohomologyVanishes still uses the retained old predicate; its formula is the same acyclic-total-tensor condition. That separate API migration is pre-existing. |

The source-only downstream tool reports the item as unknown because it is quarantined. A direct search of all Lean and quarantine files finds no current Lean importers of the item. The three archived
importers above are also the three textual declaration users. No source-library
file or target is changed. This packet does not restore or modify those separate
quarantined modules. Restoring this theorem introduces no new consumer failure.

## Status

landed 20261020T153002-L-2859128 2026-10-20 (merge of deliver/F4/Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology)
