/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-! # An already localized functor agrees with its left derived functor

Source: the localization universal property, used in blueprint order 1826, step 4
(blueprint: lem-sf-localization-left-derived-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v w u' v' w'
namespace CategoryTheory.Functor
variable {C : Type u} {D : Type v} {H : Type w}
  [Category.{u'} C] [Category.{v'} D] [Category.{w'} H]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (F : C ⥤ H) (LF G : D ⥤ H) (α : L ⋙ LF ⟶ F)
  [LF.IsLeftDerivedFunctor α W] (β : L ⋙ G ≅ F)

/-- If the underived functor already factors through localization, the universal
left derived comparison is invertible. Source: localization's fully faithful
precomposition, blueprint order 1826 (blueprint: lem-sf-localization-left-derived-comparison).
Proof: lift α followed by β⁻¹ through fully faithful precomposition to obtain LF→G.
The left-derived universal property gives G→LF. One composite is the identity by
that universal property, and the other by fully faithful precomposition. -/
def localizationLeftDerivedComparison : LF ≅ G := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W H
  let τ : LF ⟶ G := ff.preimage (α ≫ β.inv)
  let σ : G ⟶ LF := LF.leftDerivedLift α W G β.hom
  have hτ : whiskerLeft L τ = α ≫ β.inv := ff.map_preimage _
  have hσ : whiskerLeft L σ ≫ α = β.hom := LF.leftDerived_fac α W G β.hom
  refine ⟨τ, σ, ?_, ?_⟩
  · apply LF.leftDerived_ext α W
    simp only [whiskerLeft_comp, whiskerLeft_id', Category.assoc, Category.id_comp]
    rw [hσ, hτ, Category.assoc, β.inv_hom_id, Category.comp_id]
  · apply ff.map_injective
    change whiskerLeft L (σ ≫ τ) = whiskerLeft L (𝟙 G)
    rw [whiskerLeft_comp, whiskerLeft_id', hτ, ← Category.assoc, hσ, β.hom_inv_id]

/-- The comparison retains exactly the prescribed counit normalization.
Source: localization's fully faithful precomposition, blueprint order 1826
(blueprint: lem-sf-localization-left-derived-comparison). -/
theorem localizationLeftDerivedComparison_fac :
    whiskerLeft L (localizationLeftDerivedComparison L W F LF G α β).hom ≫ β.hom = α := by
  change ((whiskeringLeft C D H).obj L).map
    ((Localization.fullyFaithfulWhiskeringLeft L W H).preimage (α ≫ β.inv)) ≫ β.hom = α
  rw [Functor.FullyFaithful.map_preimage, Category.assoc, β.inv_hom_id, Category.comp_id]

end CategoryTheory.Functor
