/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.MayerVietorisOpenCompositionRestrictedSourceUnit
import WeilConjectures.AlgebraicGeometry.MayerVietorisOpenCompositionRestrictionFactors

/-! # Left-hand composition normalization

Source: Stacks Project, Tags 08FE and 0D5T.
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

set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 500000 in
-- The exact restriction factors require additional categorical instance conversions.
/-- Left-hand composition normalization to the complex-composition composite.
Source: Stacks Project, Tags 08FE, 0D5T and 079V.

Proof: Apply schemeMVOpenComposition_complex_localization to the termwise restriction J.
Naturality of the derived composition isomorphism along the inverse exact X-restriction
factor moves this factor from the source to the restricted direct image on the right.
Expand only the open-image localization and canonical open comparison. Postcompose the
unit equation with open direct image of that factor and the inverse derived restriction
comparison. Functoriality combines these three maps. This calculation involves no image
component, no exact Y-restriction factor, and no injectivity hypothesis.
The argument applies to arbitrary complexes, empty and full opens, and identity morphisms:
only functoriality, naturality and inverse-isomorphism equations are used. -/
theorem schemeMV_composition_left_normalization
    (X Y : Scheme.{u}) (h : X ⟶ Y) (W : Y.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let F := (RingedSpace.moduleDirectImage h.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)
    let R := schemeDerivedDirectImage W.ι
    (schemeMVDirectImageLocalization h).app (schemeOpenModuleImageComplex X (h ⁻¹ᵁ W) I) ≫
      (schemeDerivedDirectImage h).map (schemeMVOpenImageLocalization X (h ⁻¹ᵁ W) I) ≫
      (schemeMVOpenComparison h W (DerivedCategory.Q.obj I)).hom =
    (let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
     let J := (LX.mapHomologicalComplex (.up ℤ)).obj I
     let G := RingedSpace.moduleDirectImage (h ∣_ W).toLRSHom.toShHom
     let RY := RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom
     let b₀ := (Functor.mapHomologicalComplexCompIso
         (schemeMVUnderivedOpenComposition h W) (.up ℤ) ≪≫
       (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ RY)) (.up ℤ)).symm).hom.app J
     DerivedCategory.Q.map b₀ ≫
       (schemeMVDirectImageLocalization W.ι).app
         ((G.mapHomologicalComplex (.up ℤ)).obj J) ≫
       R.map ((schemeMVDirectImageLocalization (h ∣_ W)).app J ≫
         (schemeDerivedDirectImage (h ∣_ W)).map
           (LX.mapDerivedCategoryFactors.inv.app I) ≫
         (schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I))) := by
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ W)
  let J := (LX.mapHomologicalComplex (.up ℤ)).obj I
  let β := (schemeMVDirectImageComposition (h ⁻¹ᵁ W).ι h).symm ≪≫
    eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h W).symm) ≪≫
    schemeMVDirectImageComposition (h ∣_ W) W.ι
  have hc := schemeMVOpenComposition_restricted_source_unit X Y h W β rfl I
  have hf := schemeMVOpenComposition_restriction_factors X Y h W I
  dsimp only [] at hc hf ⊢
  rw [hf]
  have hp := congrArg (fun t ↦ t ≫ (schemeDerivedDirectImage W.ι).map
    ((schemeDerivedDirectImage (h ∣_ W)).map (LX.mapDerivedCategoryFactors.inv.app I) ≫
      (schemeMVOpenRestrictionComparison h W).inv.app (DerivedCategory.Q.obj I))) hc
  simpa only [Functor.map_comp, Category.assoc] using hp

end AlgebraicGeometry
