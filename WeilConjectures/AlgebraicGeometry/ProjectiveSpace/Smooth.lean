/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-!
# Projective space is smooth

For a finite type `n` and a scheme `S`, the projective space `ℙ(n; S) ⟶ S` is smooth of relative
dimension `|n| - 1` (`AlgebraicGeometry.ProjectiveSpace.smoothOfRelativeDimension`): it is
covered by the standard opens `D₊(Tᵢ)`, each isomorphic over `S` to the affine space
`𝔸({j // j ≠ i}; S)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveSpace

/-- **Projective space is smooth**: `ℙ(n; S) ⟶ S` is smooth of relative dimension `|n| - 1`,
since on the standard open `D₊(Tᵢ)` it is the affine space `𝔸({j // j ≠ i}; S)`. -/
instance smoothOfRelativeDimension (n : Type u) [Fintype n] (S : Scheme.{u}) :
    SmoothOfRelativeDimension (Fintype.card n - 1) (ℙ(n; S) ↘ S) := by
  refine smoothOfRelativeDimension_of_forall_exists_mem _ _ fun y ↦ ?_
  have : y ∈ (⊤ : ℙ(n; S).Opens) := trivial
  rw [← iSup_standardOpen, TopologicalSpace.Opens.mem_iSup] at this
  obtain ⟨i, hi⟩ := this
  refine ⟨_, hi, ?_⟩
  rw [← standardOpenIso_hom_over]
  have h : Nat.card {j : n // j ≠ i} = Fintype.card n - 1 := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have := AffineSpace.smoothOfRelativeDimension_over {j : n // j ≠ i} S
  rw [h] at this
  have h0 : SmoothOfRelativeDimension (0 + (Fintype.card n - 1))
      ((standardOpenIso n S i).hom ≫ 𝔸({j : n // j ≠ i}; S) ↘ S) := inferInstance
  rwa [zero_add] at h0

/-- `ℙⁿ_S = ℙ(Fin (n + 1); S) ⟶ S` is smooth of relative dimension `n`. -/
instance smoothOfRelativeDimension_fin (n : ℕ) (S : Scheme.{u}) :
    SmoothOfRelativeDimension n (ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S) := by
  have := smoothOfRelativeDimension (ULift.{u} (Fin (n + 1))) S
  rwa [Fintype.card_ulift, Fintype.card_fin, Nat.add_sub_cancel] at this

end AlgebraicGeometry.ProjectiveSpace
