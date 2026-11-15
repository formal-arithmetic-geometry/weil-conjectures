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

## References

* [Stacks, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
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

-- Keep the composition calculation independent of the concrete derived functors.
private lemma schemeMV_composition_postcompose
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {P₁ P₂ P₃ P₄ : D} {Q₁ Q₂ Q₃ : C}
    (a : P₁ ⟶ P₂) (b : P₂ ⟶ P₃) (c : P₃ ⟶ R.obj Q₁)
    (d : P₂ ⟶ R.obj Q₃) (e : P₁ ⟶ P₄) (f : P₄ ⟶ R.obj Q₂)
    (g : Q₂ ⟶ Q₁) (t : Q₁ ⟶ Q₃)
    (hf : d = b ≫ c ≫ R.map t) (hc : a ≫ b ≫ c = e ≫ f ≫ R.map g) :
    a ≫ d = e ≫ f ≫ R.map (g ≫ t) := by
  rw [hf, R.map_comp]
  simpa only [Category.assoc] using congrArg (fun v ↦ v ≫ R.map t) hc

set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- Left-hand composition normalization to the complex-composition composite.
(Stacks, Tags 08FE, 0D5T, 079V) -/
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
  let β := (schemeMVDirectImageComposition (h ⁻¹ᵁ W).ι h).symm ≪≫
    eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h W).symm) ≪≫
    schemeMVDirectImageComposition (h ∣_ W) W.ι
  have hc := schemeMVOpenComposition_restricted_source_unit X Y h W β rfl I
  have hf := schemeMVOpenComposition_restriction_factors X Y h W I
  dsimp only [] at hc hf ⊢
  exact schemeMV_composition_postcompose (schemeDerivedDirectImage W.ι)
    _ _ _ _ _ _ _ _ hf hc

end AlgebraicGeometry
