/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExternalIhom

/-!
# Naturality of the specified external internal Hom comparison

Source: latest blueprint, prop-trf-external-hom.proof.md, evaluation transpose;
sub-step of lem-sf-kv-exact-comparisons, Step 8.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace CategoryTheory.MonoidalClosed

variable {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  [MonoidalCategory D₁] [MonoidalClosed D₁]
  [MonoidalCategory D₂] [MonoidalClosed D₂]
  (F₁ : D₁ ⥤ C) (F₂ : D₂ ⥤ C) [F₁.LaxMonoidal] [F₂.LaxMonoidal]

/-- Naturality in the two targets follows by uncurrying, middle-four naturality,
monoidality, and evaluation naturality. Source: the evaluation definition of beta
in sk-def-sf-kv-maps (iii) (blueprint: lem-sf-external-hom-comparison-naturality). -/
@[reassoc]
theorem externalIhomMap_naturality_targets (E₁ : D₁) (E₂ : D₂)
    {L₁ L₁' : D₁} {L₂ L₂' : D₂} (f₁ : L₁ ⟶ L₁') (f₂ : L₂ ⟶ L₂') :
    (F₁.map ((ihom E₁).map f₁) ⊗ₘ F₂.map ((ihom E₂).map f₂)) ≫
        externalIhomMap F₁ F₂ E₁ L₁' E₂ L₂' =
      externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂ ≫
        (ihom (F₁.obj E₁ ⊗ F₂.obj E₂)).map (F₁.map f₁ ⊗ₘ F₂.map f₂) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_right,
    uncurry_externalIhomMap, uncurry_externalIhomMap,
    tensorμ_natural_right_assoc]
  simp only [Category.assoc, tensorHom_comp_tensorHom]
  congr 1
  congr 1 <;>
    rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp,
      ihom.ev_naturality, Functor.map_comp]

/-- Naturality in the two sources is evaluation dinaturality after uncurrying.
Source: the evaluation definition of beta in sk-def-sf-kv-maps (iii)
(blueprint: lem-sf-external-hom-comparison-naturality). -/
@[reassoc]
theorem externalIhomMap_naturality_sources {E₁ E₁' : D₁} {E₂ E₂' : D₂}
    (f₁ : E₁' ⟶ E₁) (f₂ : E₂' ⟶ E₂) (L₁ : D₁) (L₂ : D₂) :
    (F₁.map ((pre f₁).app L₁) ⊗ₘ F₂.map ((pre f₂).app L₂)) ≫
        externalIhomMap F₁ F₂ E₁' L₁ E₂' L₂ =
      externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂ ≫
        (pre (F₁.map f₁ ⊗ₘ F₂.map f₂)).app (F₁.obj L₁ ⊗ F₂.obj L₂) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_pre_app,
    uncurry_externalIhomMap, uncurry_externalIhomMap,
    tensorμ_natural_right_assoc, tensorμ_natural_left_assoc]
  simp only [tensorHom_comp_tensorHom]
  congr 1
  congr 1 <;>
    rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← Functor.map_comp,
      id_tensor_pre_app_comp_ev, Functor.map_comp,
      Functor.LaxMonoidal.μ_natural_left_assoc]

/-- The comparison as a natural transformation in its first target.
Source: sk-def-sf-kv-maps (iii)
(blueprint: lem-sf-external-hom-comparison-naturality). -/
noncomputable def externalIhomTargetLeft (E₁ : D₁) (E₂ L₂ : D₂) :
    ihom E₁ ⋙ F₁ ⋙ tensorRight (F₂.obj ((ihom E₂).obj L₂)) ⟶
      F₁ ⋙ tensorRight (F₂.obj L₂) ⋙ ihom (F₁.obj E₁ ⊗ F₂.obj E₂) where
  app L₁ := externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂
  naturality L₁ L₁' f := by
    simpa using externalIhomMap_naturality_targets F₁ F₂ E₁ E₂ f (𝟙 L₂)

/-- The comparison as a natural transformation in its second target.
Source: sk-def-sf-kv-maps (iii)
(blueprint: lem-sf-external-hom-comparison-naturality). -/
noncomputable def externalIhomTargetRight (E₁ L₁ : D₁) (E₂ : D₂) :
    ihom E₂ ⋙ F₂ ⋙ tensorLeft (F₁.obj ((ihom E₁).obj L₁)) ⟶
      F₂ ⋙ tensorLeft (F₁.obj L₁) ⋙ ihom (F₁.obj E₁ ⊗ F₂.obj E₂) where
  app L₂ := externalIhomMap F₁ F₂ E₁ L₁ E₂ L₂
  naturality L₂ L₂' f := by
    simpa using externalIhomMap_naturality_targets F₁ F₂ E₁ E₂ (𝟙 L₁) f

/-- The comparison as a natural transformation in the opposite of its first source.
Source: sk-def-sf-kv-maps (iii)
(blueprint: lem-sf-external-hom-comparison-naturality). -/
noncomputable def externalIhomSourceLeft (L₁ : D₁) (E₂ L₂ : D₂) :
    internalHom.flip.obj L₁ ⋙ F₁ ⋙ tensorRight (F₂.obj ((ihom E₂).obj L₂)) ⟶
      (F₁ ⋙ tensorRight (F₂.obj E₂)).op ⋙
        internalHom.flip.obj (F₁.obj L₁ ⊗ F₂.obj L₂) where
  app E₁ := externalIhomMap F₁ F₂ E₁.unop L₁ E₂ L₂
  naturality E₁ E₁' f := by
    simpa using externalIhomMap_naturality_sources F₁ F₂ f.unop (𝟙 E₂) L₁ L₂

/-- The comparison as a natural transformation in the opposite of its second source.
Source: sk-def-sf-kv-maps (iii)
(blueprint: lem-sf-external-hom-comparison-naturality). -/
noncomputable def externalIhomSourceRight (E₁ L₁ : D₁) (L₂ : D₂) :
    internalHom.flip.obj L₂ ⋙ F₂ ⋙ tensorLeft (F₁.obj ((ihom E₁).obj L₁)) ⟶
      (F₂ ⋙ tensorLeft (F₁.obj E₁)).op ⋙
        internalHom.flip.obj (F₁.obj L₁ ⊗ F₂.obj L₂) where
  app E₂ := externalIhomMap F₁ F₂ E₁ L₁ E₂.unop L₂
  naturality E₂ E₂' f := by
    simpa using externalIhomMap_naturality_sources F₁ F₂ (𝟙 E₁) f.unop L₁ L₂

end CategoryTheory.MonoidalClosed
