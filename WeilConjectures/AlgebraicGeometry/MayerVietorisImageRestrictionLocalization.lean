/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisRestrictionLocalizationChain
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenRestrictionNormalization
import WeilConjectures.AlgebraicGeometry.MayerVietorisRestrictionChainQuotientTransport

/-! # Complex localization of the open restriction square

## References

* Stacks Project, Tags 08FE, 08BV and 079V.
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

/-- Complex localization of the open restriction square (Stacks, Tags 08FE and 079V). The
four-factor unit equation is that of `schemeMVOpenRestriction_unit_normalization`. -/
theorem schemeMV_image_restriction_localization
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (schemeMVRestrictionLocalizationChain X Y h W I) ≫
      (schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I) =
    (schemeMVDerivedRestriction Y W).map ((schemeMVDirectImageLocalization h).app I) := by
  let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
  let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
  let LY := schemeOpenRestriction Y W
  let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  have hn := schemeMVOpenRestriction_unit_normalization X Y h W K
  rw [schemeMV_restriction_chain_quotient_transport]
  rw [← hn]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  simp only [K, Iso.hom_inv_id_app_assoc]
  have ha := (schemeMVOpenRestrictionComparison h W).hom.naturality
    ((DerivedCategory.quotientCompQhIso _).hom.app I)
  dsimp only [Functor.comp_map] at ha
  rw [← reassoc_of% ha]
  simp only [Iso.hom_inv_id_app]
  simp [schemeMVDirectImageLocalization, Functor.map_comp, Category.assoc]


end AlgebraicGeometry
