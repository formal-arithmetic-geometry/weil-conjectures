/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pasting of conjugate squares

Given adjunctions, a pasting of squares of left adjoints can be checked after taking conjugates
(`CategoryTheory.conjugateEquiv`), on the corresponding pasting of squares of right adjoints
(`CategoryTheory.conjugateEquiv_paste_eq`). This is how compatibilities of isomorphisms between
pullback functors of sheaves are deduced from the (objectwise obvious) compatibilities of the
corresponding isomorphisms between pushforward functors.
-/

@[expose] public section

namespace CategoryTheory

open Functor

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

/-- The conjugate of the inverse associator is the inverse associator. -/
lemma conjugateEquiv_associator_inv
    {L₀₁ : C₀ ⥤ C₁} {R₁₀ : C₁ ⥤ C₀} {L₁₂ : C₁ ⥤ C₂} {R₂₁ : C₂ ⥤ C₁}
    {L₂₃ : C₂ ⥤ C₃} {R₃₂ : C₃ ⥤ C₂} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (associator _ _ _).inv = (associator _ _ _).inv := by
  have h := conjugateEquiv_comp (adj₀₁.comp (adj₁₂.comp adj₂₃)) ((adj₀₁.comp adj₁₂).comp adj₂₃)
    (adj₀₁.comp (adj₁₂.comp adj₂₃)) (associator L₀₁ L₁₂ L₂₃).hom (associator L₀₁ L₁₂ L₂₃).inv
  rw [conjugateEquiv_associator_hom, Iso.inv_hom_id, conjugateEquiv_id] at h
  exact (Iso.hom_comp_eq_id (associator _ _ _)).1 h

variable {CR CS CT PR PS PT : Type*} [Category* CR] [Category* CS] [Category* CT]
  [Category* PR] [Category* PS] [Category* PT]
  {e₁ : CS ⥤ CT} {r₁ : CT ⥤ CS} {e₂ : CR ⥤ CS} {r₂ : CS ⥤ CR} {e₁₂ : CR ⥤ CT} {r₁₂ : CT ⥤ CR}
  {p₁ : PS ⥤ PT} {q₁ : PT ⥤ PS} {p₂ : PR ⥤ PS} {q₂ : PS ⥤ PR} {p₁₂ : PR ⥤ PT} {q₁₂ : PT ⥤ PR}
  {νR : CR ⥤ PR} {μR : PR ⥤ CR} {νS : CS ⥤ PS} {μS : PS ⥤ CS} {νT : CT ⥤ PT} {μT : PT ⥤ CT}
  (aE₁ : e₁ ⊣ r₁) (aE₂ : e₂ ⊣ r₂) (aE₁₂ : e₁₂ ⊣ r₁₂) (aP₁ : p₁ ⊣ q₁) (aP₂ : p₂ ⊣ q₂)
  (aP₁₂ : p₁₂ ⊣ q₁₂) (aR : νR ⊣ μR) (aS : νS ⊣ μS) (aT : νT ⊣ μT)

/-- A pasting of squares of left adjoints is determined by the corresponding pasting of the
conjugate squares of right adjoints. -/
lemma conjugateEquiv_paste_eq (Ecomp' : e₂ ⋙ e₁ ⟶ e₁₂)
    (Pcomp : p₁₂ ⟶ p₂ ⋙ p₁) (σ₁ : νS ⋙ p₁ ⟶ e₁ ⋙ νT) (σ₂ : νR ⋙ p₂ ⟶ e₂ ⋙ νS)
    (σ₁₂ : νR ⋙ p₁₂ ⟶ e₁₂ ⋙ νT)
    (h : conjugateEquiv (aE₁₂.comp aT) (aR.comp aP₁₂) σ₁₂ =
      whiskerLeft μT (conjugateEquiv aE₁₂ (aE₂.comp aE₁) Ecomp') ≫ (associator _ _ _).inv ≫
        whiskerRight (conjugateEquiv (aE₁.comp aT) (aS.comp aP₁) σ₁) r₂ ≫
        (associator _ _ _).hom ≫
        whiskerLeft q₁ (conjugateEquiv (aE₂.comp aS) (aR.comp aP₂) σ₂) ≫
        (associator _ _ _).inv ≫
        whiskerRight (conjugateEquiv (aP₂.comp aP₁) aP₁₂ Pcomp) μR) :
    σ₁₂ = whiskerLeft νR Pcomp ≫ (associator _ _ _).inv ≫ whiskerRight σ₂ p₁ ≫
      (associator _ _ _).hom ≫ whiskerLeft e₂ σ₁ ≫ (associator _ _ _).inv ≫
      whiskerRight Ecomp' νT := by
  apply (conjugateEquiv (aE₁₂.comp aT) (aR.comp aP₁₂)).injective
  rw [h, ← conjugateEquiv_comp _ (aR.comp (aP₂.comp aP₁)) _,
    ← conjugateEquiv_comp _ ((aR.comp aP₂).comp aP₁) _,
    ← conjugateEquiv_comp _ ((aE₂.comp aS).comp aP₁) _,
    ← conjugateEquiv_comp _ (aE₂.comp (aS.comp aP₁)) _,
    ← conjugateEquiv_comp _ (aE₂.comp (aE₁.comp aT)) _,
    ← conjugateEquiv_comp _ ((aE₂.comp aE₁).comp aT) _,
    conjugateEquiv_whiskerLeft, conjugateEquiv_associator_inv, conjugateEquiv_whiskerRight,
    conjugateEquiv_associator_hom, conjugateEquiv_whiskerLeft, conjugateEquiv_associator_inv,
    conjugateEquiv_whiskerRight]
  simp only [Category.assoc]

end CategoryTheory
