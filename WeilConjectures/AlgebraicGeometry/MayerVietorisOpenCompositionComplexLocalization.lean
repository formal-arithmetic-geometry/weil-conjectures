/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCompositionNormalization

/-! # The complex form of the open composition unit equation

Source: Stacks Project, Tags 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-open-composition-complex-localization).
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
/-- The open composition unit equation on any complex on the inverse-image open.
Source: Stacks Project, Tags 08FE and 0D5T.
Proof: apply schemeMVOpenComposition_unit_normalization to the homotopy quotient of J.
The components of mapHomotopyCategoryFactors and quotientCompQhIso are identities.
Expand schemeMVDirectImageLocalization and use those component identities to identify
its units with the homotopy units. The homotopy composition comparison is the quotient
of the displayed complex comparison, by mapHomotopyCategoryCompIso. Functoriality of Q
and the naturality of the quotient comparison give the displayed equation. There is
no restriction factor, counit, or K-injectivity hypothesis. This applies also to the
empty open, full open, and identity h because the same quotient identities apply.
(blueprint: lem-pc-mayer-vietoris-open-composition-complex-localization). -/
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
  dsimp +instances [schemeMVDirectImageLocalization, schemeMVHomotopyOpenComposition,
    Functor.mapHomotopyCategoryFactors, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryCompIso, Quotient.natIsoLift, Quotient.natTransLift,
    DerivedCategory.Q, DerivedCategory.Qh, schemeDerivedDirectImage,
    RingedSpace.derivedModuleDirectImage, instCategoryDerivedCategory] at hn ⊢
  simp +instances only [Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc]
  erw [RX.rightDerivedFunctor.map_id (DerivedCategory.Q.obj J),
    G.rightDerivedFunctor.map_id (DerivedCategory.Q.obj J)]
  erw [F.rightDerivedFunctor.map_id _, RY.rightDerivedFunctor.map_id _]
  erw [F.rightDerivedFunctor.map_id (RX.rightDerivedFunctor.obj (DerivedCategory.Q.obj J)),
    RY.rightDerivedFunctor.map_id (G.rightDerivedFunctor.obj (DerivedCategory.Q.obj J))]
  repeat erw [Category.id_comp]
  repeat erw [Category.comp_id]
  simp only [Functor.map_comp, Category.assoc] at hn
  exact hn

end AlgebraicGeometry
