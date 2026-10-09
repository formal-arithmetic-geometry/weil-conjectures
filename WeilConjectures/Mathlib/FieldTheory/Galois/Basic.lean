/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow fixed fields

For a finite Galois extension `N/K` and a prime `ℓ`, the fixed field `L` of a Sylow
`ℓ`-subgroup of `Gal(N/K)` has degree `[L : K]` prime to `ℓ`, and `Gal(N/L)` is an `ℓ`-group.
-/

@[expose] public section

open IntermediateField

/-- **Sylow fixed fields.** For a finite Galois extension `N/K` and a prime `ℓ`, there is an
intermediate field `L` with `[L : K]` prime to `ℓ` such that `Gal(N/L)` is an `ℓ`-group: the
fixed field of a Sylow `ℓ`-subgroup of `Gal(N/K)`. -/
theorem IsGalois.exists_not_dvd_finrank_isPGroup (K N : Type*) [Field K] [Field N]
    [Algebra K N] [FiniteDimensional K N] [IsGalois K N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ L : IntermediateField K N, ¬ ℓ ∣ Module.finrank K L ∧ IsPGroup ℓ (N ≃ₐ[L] N) := by
  obtain ⟨P⟩ : Nonempty (Sylow ℓ (N ≃ₐ[K] N)) := inferInstance
  refine ⟨fixedField (P : Subgroup (N ≃ₐ[K] N)), ?_, ?_⟩
  · have h₁ := finrank_fixedField_eq_card (P : Subgroup (N ≃ₐ[K] N))
    have h₂ := Module.finrank_mul_finrank K (fixedField (P : Subgroup (N ≃ₐ[K] N))) N
    have h₃ := IsGalois.card_aut_eq_finrank K N
    have h₄ := (P : Subgroup (N ≃ₐ[K] N)).index_mul_card
    have hpos : 0 < Nat.card (P : Subgroup (N ≃ₐ[K] N)) := Nat.card_pos
    have : Module.finrank K (fixedField (P : Subgroup (N ≃ₐ[K] N))) =
        (P : Subgroup (N ≃ₐ[K] N)).index := by
      rw [h₁] at h₂
      exact Nat.eq_of_mul_eq_mul_right hpos (h₂.trans (h₃.symm.trans h₄.symm))
    rw [this]
    exact P.not_dvd_index
  · have hP : IsPGroup ℓ (fixingSubgroup (fixedField (P : Subgroup (N ≃ₐ[K] N)))) := by
      rw [fixingSubgroup_fixedField]
      exact P.isPGroup'
    exact hP.of_equiv (fixingSubgroupEquiv _)
