/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCompositionNormalization

/-! # The complex form of the open composition unit equation

## References

* Stacks Project, Tags 08FE and 0D5T.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian
set_option maxHeartbeats 700000 in
-- Transport through the complex and homotopy localization interfaces.
/-- The open composition unit equation on any complex on the inverse-image open
(Stacks, Tags 08FE and 0D5T). -/
theorem schemeMVOpenComposition_complex_localization
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ W).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ W) ⋙ schemeDerivedDirectImage W.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ W).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h W).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ W) W.ι)
    (J : CochainComplex
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ W).toScheme.toRingedSpace)) ℤ) :
    let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ W).ι.toLRSHom.toShHom
    let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
    let RY := RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom
    let b₀ := (Functor.mapHomologicalComplexCompIso
        (schemeMVUnderivedOpenComposition h W) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app J
    (schemeMVDirectImageLocalization h).app
        ((RX.mapHomologicalComplex (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage h).map
        ((schemeMVDirectImageLocalization (h ⁻¹ᵁ W).ι).app J) ≫
      β.hom.app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map b₀ ≫
      (schemeMVDirectImageLocalization W.ι).app
        ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage W.ι).map
        ((schemeMVDirectImageLocalization (h ∣_ W)).app J) := by
  let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
  let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ W).ι.toLRSHom.toShHom
  let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
  let RY := RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom
  have hn := schemeMVOpenComposition_unit_normalization X Y h W β hβ
    ((HomotopyCategory.quotient _ (.up ℤ)).obj J)
  let b₀ := (Functor.mapHomologicalComplexCompIso
      (schemeMVUnderivedOpenComposition h W) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app J
  have hb : (schemeMVHomotopyOpenComposition h W).hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj J) =
      (HomotopyCategory.quotient _ (.up ℤ)).map b₀ := by
    dsimp [b₀, schemeMVHomotopyOpenComposition, Functor.mapHomotopyCategoryCompIso,
      Quotient.natIsoLift, Quotient.natTransLift]
    rw [Functor.map_comp]
    rfl
  dsimp only at hn ⊢
  rw [hb] at hn
  dsimp only [schemeMVDirectImageLocalization, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Functor.comp_obj, Functor.map_comp, Category.assoc]
  repeat erw [DerivedCategory.Qh.map_id]
  simp only [Category.id_comp]
  erw [← (schemeDerivedDirectImage h).map_comp_assoc, Iso.hom_inv_id_app,
    (schemeDerivedDirectImage h).map_id, Category.id_comp]
  erw [← (schemeDerivedDirectImage W.ι).map_comp_assoc, Iso.hom_inv_id_app,
    (schemeDerivedDirectImage W.ι).map_id, Category.id_comp]
  erw [β.hom.naturality, DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  repeat erw [Category.id_comp]
  have ht := congrArg (fun t ↦
    (DerivedCategory.quotientCompQhIso _).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj ((RX.mapHomologicalComplex (.up ℤ)).obj J)) ≫
        t ≫ (schemeDerivedDirectImage W.ι).map
          ((schemeDerivedDirectImage (h ∣_ W)).map
            ((DerivedCategory.quotientCompQhIso _).hom.app J))) hn
  dsimp +instances [F, RX, G, RY, b₀, DerivedCategory.Q, DerivedCategory.Qh,
    schemeDerivedDirectImage, RingedSpace.derivedModuleDirectImage,
    instCategoryDerivedCategory] at ht ⊢
  simpa only [Functor.comp_map, Functor.mapHomotopyCategory_obj,
    HomotopyCategory.quotient_obj_as, Category.assoc] using ht

end AlgebraicGeometry
