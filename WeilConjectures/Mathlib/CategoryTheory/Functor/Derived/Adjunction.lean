/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Changing the left derived functor in a derived adjunction

If `α : L₁ ⋙ G' ⟶ G ⋙ L₂` factors as `L₁ ⋙ G' ≅ L₁ ⋙ G'' ⟶ G ⋙ L₂` through an
isomorphism `e : G' ≅ G''`, the derived adjunction `G' ⊣ F'` built from `α` is the derived
adjunction `G'' ⊣ F'` built from the second factor, transported along `e`.
-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  {G' G'' : D₁ ⥤ D₂} {F' : D₂ ⥤ D₁}
  (α : L₁ ⋙ G' ⟶ G ⋙ L₂) (α' : L₁ ⋙ G'' ⟶ G ⋙ L₂) (β : F ⋙ L₁ ⟶ L₂ ⋙ F')

namespace Adjunction

open CategoryTheory.Functor

lemma derived_eq_ofNatIsoLeft (e : G' ≅ G'') (hα : α = whiskerLeft L₁ e.hom ≫ α')
    [G'.IsLeftDerivedFunctor α W₁] [G''.IsLeftDerivedFunctor α' W₁]
    [F'.IsRightDerivedFunctor β W₂]
    [(G' ⋙ F').IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫ whiskerRight α F') W₁]
    [(F' ⋙ G').IsRightDerivedFunctor (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂]
    [(G'' ⋙ F').IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫ whiskerRight α' F') W₁]
    [(F' ⋙ G'').IsRightDerivedFunctor
      (whiskerRight β G'' ≫ (Functor.associator _ _ _).hom) W₂] :
    adj.derived W₁ W₂ α β = (adj.derived W₁ W₂ α' β).ofNatIsoLeft e.symm := by
  apply Adjunction.ext_counit
  apply (F' ⋙ G').rightDerived_ext (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂
  ext X
  subst hα
  have h₁ := adj.derivedε_fac_app W₂ (whiskerLeft L₁ e.hom ≫ α') β X
  have h₂ := adj.derivedε_fac_app W₂ α' β X
  have h₃ := e.hom.naturality (β.app X)
  dsimp at h₁ h₂ h₃ ⊢
  simp only [derived_counit, ofNatIsoLeft_counit, Iso.symm_inv, NatTrans.comp_app,
    whiskerLeft_app, Category.comp_id]
  rw [h₁, reassoc_of% h₃, h₂, Category.assoc]

end Adjunction

end CategoryTheory
