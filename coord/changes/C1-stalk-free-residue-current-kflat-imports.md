# AlgebraicGeometry.Scheme.nonempty_stalkFree_residueCohomology_linearEquiv

## Reason

Restore the quarantined item after its residue-comparison dependency was restored by F4.
The archived proof imports the old Sheaf KFlatResolution and KFlatStalkCriterion modules.
Their upstream equivalents use IsKFlatTensor, which is the predicate required by the
restored KFlatStalkResidueCohomology. Switch both private proof imports to the upstream
modules. Preserve every public import, the complete theorem signature, and its proof body.
This repairs the imported K-flat interface; it is not merely a rebase or a no-op restoration.
No definition or theorem statement changes.

## Old

```lean
theorem nonempty_stalkFree_residueCohomology_linearEquiv
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ E)
    (K : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (b : ℤ) (hb : K.IsStrictlyLE b)
    (hfree : ∀ j : ℤ, Module.Free (X.presheaf.stalk x) (K.X j))
    (eK : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)) (i : ℤ) :
    Nonempty (derivedFiberCohomology X E i x ≃ₗ[IsLocalRing.ResidueField
      (X.presheaf.stalk x)]
        ((((ModuleCat.extendScalars
          (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).homology i))
```

Private imports:
```lean
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatStalkCriterion
```

## New

```lean
theorem nonempty_stalkFree_residueCohomology_linearEquiv
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) (x : X)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    [HasDerivedCategory.{v} (ModuleCat.{u} (X.presheaf.stalk x))]
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eG : DerivedCategory.Q.obj G ≅ E)
    (K : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (b : ℤ) (hb : K.IsStrictlyLE b)
    (hfree : ∀ j : ℤ, Module.Free (X.presheaf.stalk x) (K.X j))
    (eK : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)) (i : ℤ) :
    Nonempty (derivedFiberCohomology X E i x ≃ₗ[IsLocalRing.ResidueField
      (X.presheaf.stalk x)]
        ((((ModuleCat.extendScalars
          (IsLocalRing.residue (X.presheaf.stalk x))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).homology i))
```

Private imports:
```lean
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StalkFreeResidueCohomologyComparison | C1 | Restored complete proof with current upstream K-flat interfaces. |
| Sheaf.AlgebraicGeometry.StrictPerfectStalkFiberData | unclaimed, quarantined | The declaration type and public imports are identical to the archive; its call needs no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectFiniteResidueCohomologyFinite | unclaimed, quarantined | The declaration type and public imports are identical to the archive; its call needs no adaptation. |

The downstream tool reports the module as unknown while it is quarantined. Searching
both lean/ and quarantine/ finds precisely the two archived importers listed above;
both are also textual users of the declaration. Neither consumer is changed by this
packet, and neither acquires a new error from these private import replacements.
The DAG attachment and all mathematical dependencies are retained.

## Status

landed 20261020T154040-L-3034066 2026-10-20 (merge of deliver/C1/Sheaf.AlgebraicGeometry.StalkFreeResidueCohomologyComparison)
