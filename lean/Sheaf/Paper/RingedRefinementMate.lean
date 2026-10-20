/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transposing a coefficient-compatible refinement map

Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement, counit calculation
(blueprint: lem-pur-refinement-coefficient-mate).
-/

@[expose] public section
set_option autoImplicit false

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory

namespace CategoryTheory

/-- A compatible square between the left-adjoint refinement maps gives the square
between their right-adjoint transposes and the coefficient mate. No mate is inverted.
Source: Bhatt--Scholze 6.7.6--6.7.7, coefficient supplement, Step 6 of
lem-pur-ringed-refinement-coefficient-square
(blueprint: lem-pur-refinement-coefficient-mate).
Proof: apply the inverse Hom bijection for the second adjunction. Counit naturality
moves the last comparison outside the transpose. The defining mate/counit equation
replaces the middle mate by the scalar image of the first counit. Naturality of the
left comparison then combines this counit with the first refinement transpose,
recovering its original map. The other transpose is the second original map after
the left comparison. The given compatibility equates these expressions. -/
theorem refinement_coefficient_mate
    {C₁ : Type u₁} {D₁ : Type u₂} {C₂ : Type u₃} {D₂ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} D₁]
    [Category.{v₃} C₂] [Category.{v₄} D₂]
    {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {S : C₁ ⥤ C₂} {T : D₁ ⥤ D₂} (c : S ⋙ L₂ ⟶ L₁ ⋙ T)
    {M : C₁} {N : D₁} {M' : C₂} {N' : D₂}
    (h₁ : L₁.obj M ⟶ N) (h₂ : L₂.obj M' ⟶ N')
    (δ₁ : T.obj N ⟶ N') (δ₂ : S.obj M ⟶ M')
    (h : c.app M ≫ T.map h₁ ≫ δ₁ = L₂.map δ₂ ≫ h₂) :
    S.map (adj₁.homEquiv _ _ h₁) ≫
        (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ c)).natTrans.app N ≫ R₂.map δ₁ =
      δ₂ ≫ adj₂.homEquiv _ _ h₂ := by
  apply (adj₂.homEquiv _ _).symm.injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit,
    mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ c) N]
  change (L₂.map (S.map (adj₁.homEquiv _ _ h₁)) ≫
      c.app (R₁.obj N) ≫ T.map (adj₁.counit.app N)) ≫ δ₁ = _
  have hn := c.naturality (adj₁.homEquiv _ _ h₁)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← Category.assoc (T.map (L₁.map (adj₁.homEquiv _ _ h₁))), ← T.map_comp]
  have hc : L₁.map (adj₁.homEquiv _ _ h₁) ≫ adj₁.counit.app N = h₁ :=
    (adj₁.homEquiv _ _).symm_apply_apply h₁
  rw [hc]
  exact h

end CategoryTheory
