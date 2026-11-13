/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainMap
import WeilConjectures.AlgebraicGeometry.MayerVietorisImageLocalizationCompatibility
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian
set_option maxHeartbeats 500000 in
-- Transport through the three derived comparison functors needs extra reduction heartbeats.
/-- The restriction-induced intersection component realizes the canonical derived comparison
(Stacks, Tags 08FE, 08BV and 0D5T). -/
theorem schemeMV_image_resolution_comparison_intersection
    (X Y : Scheme.{u}) (h : X ⟶ Y) (U V : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (f : ((RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj (schemeMVResolution X E) ⟶
        schemeMVResolution Y ((schemeDerivedDirectImage h).obj E))
    (hf : (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
        (schemeMVResolution X E)).hom ≫ DerivedCategory.Q.map f ≫
        (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom =
      (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).hom)
    [(schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))
      (schemeMVResolution X E)).IsKInjective] :
    let I := schemeMVResolution X E
    let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
    let m := schemeMVImageChainMap (h := h) U V I J f
    (schemeDerivedDirectImage h).map
        (((schemeMVDerivedRestriction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V))) ⋙
            schemeDerivedDirectImage ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)).ι).map
            (schemeMVResolutionIso X E).inv ≫
          (schemeOpenModuleImageComplexComparison X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I
            (schemeMVAdjunction X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)))).inv) ≫
        (RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
          (schemeOpenModuleImageComplex X ((h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V)) I)).hom ≫
        DerivedCategory.Q.map m.τ₃ =
      (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
        (((schemeMVDerivedRestriction Y (U ⊓ V)) ⋙
            schemeDerivedDirectImage (U ⊓ V).ι).map
            (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).inv ≫
          (schemeOpenModuleImageComplexComparison Y (U ⊓ V) J
            (schemeMVAdjunction Y (U ⊓ V))).inv) := by
  let I := schemeMVResolution X E
  let J := schemeMVResolution Y ((schemeDerivedDirectImage h).obj E)
  let H := (schemeMVDerivedRestriction Y (U ⊓ V)) ⋙ schemeDerivedDirectImage (U ⊓ V).ι
  let a := RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom I
  let b := schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)
  let c := schemeOpenModuleImageComplexComparison Y (U ⊓ V) J
    (schemeMVAdjunction Y (U ⊓ V))
  have hn : (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).inv ≫
      a.hom ≫ DerivedCategory.Q.map f = b.inv := by
    apply (cancel_mono b.hom).mp
    simp only [Category.assoc, b.inv_hom_id]
    change (schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).inv ≫
      ((RingedSpace.derivedModuleDirectImageKInjectiveIso h.toLRSHom.toShHom
        (schemeMVResolution X E)).hom ≫ DerivedCategory.Q.map f ≫
        (schemeMVResolutionIso Y ((schemeDerivedDirectImage h).obj E)).hom) = _
    rw [hf, ← (schemeDerivedDirectImage h).map_comp, Iso.inv_hom_id]
    exact (schemeDerivedDirectImage h).map_id E
  have hp : h ⁻¹ᵁ (U ⊓ V) = (h ⁻¹ᵁ U) ⊓ (h ⁻¹ᵁ V) := rfl
  have : (schemeOpenModuleImageComplex X (h ⁻¹ᵁ (U ⊓ V)) I).IsKInjective := by
    rw [hp]
    infer_instance
  have hl := schemeMV_image_localization_compatibility X Y h (U ⊓ V) I E
    (schemeMVResolutionIso X E)
  have hnat := schemeMVOpenImageLocalization_naturality Y (U ⊓ V) f
  rw [schemeMVOpenImageLocalization_eq Y (U ⊓ V) J] at hnat
  dsimp only at hl hnat
  dsimp only
  change _ ≫ _ ≫ DerivedCategory.Q.map (schemeMVImageComponent h (U ⊓ V) I J f) = _
  rw [schemeMVImageComponent_factor, DerivedCategory.Q.map_comp]
  apply (cancel_mono c.hom).mp
  simp only [Category.assoc]
  change _ ≫ _ ≫ (DerivedCategory.Q.map _ ≫
    DerivedCategory.Q.map _ ≫ c.hom) =
    (schemeMVOpenComparison h (U ⊓ V) E).hom ≫ H.map b.inv ≫ c.inv ≫ c.hom
  erw [c.inv_hom_id, Category.comp_id]
  dsimp only [c]
  erw [hnat]
  simp only [Scheme.Hom.preimage_inf] at hl
  have hh := congrArg (fun t ↦ t ≫ H.map (DerivedCategory.Q.map f)) hl
  simp only [Category.assoc] at hh
  refine hh.trans ?_
  change (schemeMVOpenComparison h (U ⊓ V) E).hom ≫
    H.map ((schemeDerivedDirectImage h).map (schemeMVResolutionIso X E).inv ≫ a.hom) ≫
      H.map (DerivedCategory.Q.map f) = _
  rw [← H.map_comp, Category.assoc, hn]

end AlgebraicGeometry
