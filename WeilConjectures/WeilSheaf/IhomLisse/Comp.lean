/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.IhomCurry
public import WeilConjectures.WeilSheaf.IhomLisse.UpperStarComparison

/-!
# Internal composition of internal homs of `ℓ`-adic sheaves

The internal composition `𝓗om(N, K) ⟶ 𝓗om(𝓗om(M, N), 𝓗om(M, K))`, `g ↦ (f ↦ g ∘ f)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.ihomComp`), characterised by its uncurried form
`(g ⊗ f) ⊗ m ↦ g (f m)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime] {Z : Scheme.{u}}

attribute [local instance] Sheaf.symmetricCategory

/-- The evaluation `𝓗om(M, N) ⊗ M ⟶ N` is linear in `M`. -/
lemma isLinearRight_evaluation (M N : AdicSheaf l Z) :
    Mod.IsLinearRight (X := ((AdicSheaf.ihom M).obj N).X) (Mod.evaluation M N) := by
  rw [Mod.IsLinearRight, Mod.whiskerLeft_act_evaluation]
  simp only [Mod.rightAct, comp_whiskerRight, Category.assoc]
  rw [Mod.act_whiskerRight_evaluation]

/-- The uncurried internal composition `(g ⊗ f) ⊗ m ↦ g (f m)`. -/
noncomputable abbrev ihomCompAux (M N K : AdicSheaf l Z) :
    (((AdicSheaf.ihom N).obj K).X ⊗ ((AdicSheaf.ihom M).obj N).X) ⊗ M.X ⟶ K.X :=
  (α_ _ _ _).hom ≫ ((AdicSheaf.ihom N).obj K).X ◁ Mod.evaluation M N ≫ Mod.evaluation N K

lemma isLinearRight_ihomCompAux (M N K : AdicSheaf l Z) :
    Mod.IsLinearRight (ihomCompAux M N K) := by
  have h₁ := isLinearRight_evaluation M N
  have h₂ := isLinearRight_evaluation N K
  rw [Mod.IsLinearRight] at h₁ h₂
  rw [Mod.IsLinearRight]
  unfold ihomCompAux
  rw [associator_naturality_right_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, h₁]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [h₂, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, BraidedCategory.braiding_tensor_left_hom]
  simp only [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc]
  monoidal

/-- The internal composition, curried once: `g ⊗ f ↦ g ∘ f`. -/
noncomputable abbrev ihomCompCurry (M N K : AdicSheaf l Z) :
    ((AdicSheaf.ihom N).obj K).X ⊗ ((AdicSheaf.ihom M).obj N).X ⟶
      ((AdicSheaf.ihom M).obj K).X :=
  Mod.curry (ihomCompAux M N K) (isLinearRight_ihomCompAux M N K)

lemma ihomCompCurry_evaluation (M N K : AdicSheaf l Z) :
    ihomCompCurry M N K ▷ M.X ≫ Mod.evaluation M K = ihomCompAux M N K :=
  Mod.curry_evaluation _ _

lemma isLinearRight_ihomCompCurry (M N K : AdicSheaf l Z) :
    Mod.IsLinearRight (ihomCompCurry M N K) := by
  have h₂ := isLinearRight_evaluation N K
  rw [Mod.IsLinearRight] at h₂
  apply Mod.hom_ext_of_evaluation (D := M)
  rw [comp_whiskerRight, Category.assoc, ihomCompCurry_evaluation]
  simp only [comp_whiskerRight, Category.assoc]
  conv_rhs => rw [Mod.act_whiskerRight_evaluation, associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ihomCompCurry_evaluation]
  unfold ihomCompAux
  conv_lhs => rw [associator_naturality_middle_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Mod.act_whiskerRight_evaluation]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [h₂, associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc]
  monoidal

lemma ihomCompCurry_linear_left (M N K : AdicSheaf l Z) :
    Mod.act ((AdicSheaf.ihom N).obj K).X ▷ ((AdicSheaf.ihom M).obj N).X ≫
        ihomCompCurry M N K =
      (α_ _ _ _).hom ≫ adicConstantSheaf l Z ◁ ihomCompCurry M N K ≫
        Mod.act ((AdicSheaf.ihom M).obj K).X := by
  apply Mod.hom_ext_of_evaluation (D := M)
  rw [comp_whiskerRight, Category.assoc, ihomCompCurry_evaluation]
  simp only [comp_whiskerRight, Category.assoc]
  conv_rhs => rw [Mod.act_whiskerRight_evaluation, associator_naturality_middle_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, ihomCompCurry_evaluation]
  unfold ihomCompAux
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    Mod.act_whiskerRight_evaluation]
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- **Internal composition** `𝓗om(N, K) ⟶ 𝓗om(𝓗om(M, N), 𝓗om(M, K))`, `g ↦ (f ↦ g ∘ f)`. -/
noncomputable def ihomComp (M N K : AdicSheaf l Z) :
    (AdicSheaf.ihom N).obj K ⟶
      (AdicSheaf.ihom ((AdicSheaf.ihom M).obj N)).obj ((AdicSheaf.ihom M).obj K) :=
  AdicSheaf.curryHom (ihomCompCurry M N K) (isLinearRight_ihomCompCurry M N K)
    (ihomCompCurry_linear_left M N K)

/-- The uncurried form of the internal composition. -/
lemma ihomComp_evaluation (M N K : AdicSheaf l Z) :
    (ihomComp M N K).hom ▷ ((AdicSheaf.ihom M).obj N).X ≫
        Mod.evaluation ((AdicSheaf.ihom M).obj N) ((AdicSheaf.ihom M).obj K) =
      ihomCompCurry M N K :=
  AdicSheaf.curryHom_evaluation _ _ _

end AlgebraicGeometry.ProEtale.AdicSheaf
