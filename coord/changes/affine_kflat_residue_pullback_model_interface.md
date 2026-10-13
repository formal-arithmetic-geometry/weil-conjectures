# affine_kFlat_residuePullback_model interface commands

## Reason

The proof adds local elaboration commands (`open`, scoped options, and local
instances) needed to construct the canonical residue and derived-category
comparisons. The theorem signature and all public declarations retain their
original types and visibility. The delivery tool classifies these file-level
commands as an interface change because they are outside private declaration
bodies.

## Old

The unchanged existing signature, verbatim:

```lean
theorem affine_kFlat_residuePullback_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (U : X.Opens) (hU : IsAffineOpen U)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (hF : (HomologicalComplex.quasiIso
      (ModuleCat.{u} (X.presheaf.obj (.op U))) (.up ℤ)).kFlat F)
    (hmodel : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)).obj F)))
    (z : U) :
    let e := asIso (U.ι.residueFieldMap z) ≪≫
      (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫
        Spec.residueFieldIso (X.presheaf.obj (.op U)) (hU.isoSpec.hom z)
    Nonempty ((derivedPullback (X.fromSpecResidueField z)).obj E ≅
      DerivedCategory.Q.obj
        (((tilde.functor (X.residueField z)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.restrictScalars e.hom.hom).mapHomologicalComplex (.up ℤ)).obj
            (((ModuleCat.extendScalars
              (algebraMap (X.presheaf.obj (.op U))
                (hU.isoSpec.hom z).asIdeal.ResidueField)).mapHomologicalComplex
                  (.up ℤ)).obj F))))
```

The item imported two proof modules and had no local `open CategoryTheory.Limits`,
transparency options, additive-instance setup, or generic complex-comparison helper.

## New

The same signature is retained, verbatim:

```lean
theorem affine_kFlat_residuePullback_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (U : X.Opens) (hU : IsAffineOpen U)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (hF : (HomologicalComplex.quasiIso
      (ModuleCat.{u} (X.presheaf.obj (.op U))) (.up ℤ)).kFlat F)
    (hmodel : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)).obj F)))
    (z : U) :
    let e := asIso (U.ι.residueFieldMap z) ≪≫
      (asIso (hU.isoSpec.hom.residueFieldMap z)).symm ≪≫
        Spec.residueFieldIso (X.presheaf.obj (.op U)) (hU.isoSpec.hom z)
    Nonempty ((derivedPullback (X.fromSpecResidueField z)).obj E ≅
      DerivedCategory.Q.obj
        (((tilde.functor (X.residueField z)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.restrictScalars e.hom.hom).mapHomologicalComplex (.up ℤ)).obj
            (((ModuleCat.extendScalars
              (algebraMap (X.presheaf.obj (.op U))
                (hU.isoSpec.hom z).asIdeal.ResidueField)).mapHomologicalComplex
                  (.up ℤ)).obj F))))
```

The item imports the local K-flat comparison and its required proof modules; adds
local namespace openings and scoped elaboration options; registers local additive
instances; and defines a private `mapComplexComparison` helper. These commands are
used only while elaborating the item and do not add names visible to importers.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel | F1 | Only proof elaboration changes; public theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.AffineBoundedAboveFiberBettiComparison | unclaimed | Imports the proved theorem; unchanged signature and proof interface. |
| TargetsCheck | maintainer | Reaches the item through its target import closure; no interface change. |

## Status

landed 20261013T152728-L-1015279 2026-10-13 (merge of deliver/F1/Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel)
