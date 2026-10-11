/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Finite direct sums and induced Frobenius modules

The geometric stalk of the direct image `g_*F` along a finite morphism `g` at a closed point `y`
is the direct sum, over the closed points `x` above `y`, of the Frobenius cycles of length
`e = [κ(x) : κ(y)]` through the stalk `F_x̄`: `e` copies of `F_x̄`, cyclically permuted by the
Frobenius `F_y`, whose `e`-th power acts on each copy by the local Frobenius `F_x`. This file
provides the two linear-algebra constructions and their weights.

## Main definitions

- `FrobeniusModule.pi`: the direct sum `⨁ᵢ Mᵢ` of a finite family, with the diagonal Frobenius.
- `FrobeniusModule.induced`: the Frobenius cycle `M^e` of length `e` through `M`, with the
  block-cyclic Frobenius `(v₀, …, v_{e-1}) ↦ (F v_{e-1}, v₀, …, v_{e-2})`.

## Main statements

- `FrobeniusModule.IsPureOfWeight.pi`: a finite direct sum of modules pure of weight `w` is
  pure of weight `w`.
- `FrobeniusModule.hasEigenvalue_pow_of_hasEigenvalue_induced`: if `λ` is an eigenvalue of the
  block-cyclic Frobenius of `M^e`, then `λ ^ e` is an eigenvalue of the Frobenius of `M`.
- `FrobeniusModule.IsPureOfWeight.induced`: if `M` is pure of weight `w` relative to `q ^ e`,
  then the cycle `M^e` is pure of weight `w` relative to `q`.
-/

@[expose] public section

universe u v t

namespace FrobeniusModule

variable {K : Type v} [Field K]

section Pi

variable {ι : Type t} [Finite ι]

/-- The direct sum `⨁ᵢ Mᵢ` of a finite family of Frobenius modules, with the Frobenius acting
componentwise. -/
noncomputable def pi (M : ι → FrobeniusModule.{u, v} K) : FrobeniusModule.{max t u, v} K where
  carrier := (i : ι) → (M i).carrier
  frobenius := LinearEquiv.piCongrRight fun i ↦ (M i).frobenius

@[simp]
lemma pi_frobenius_apply (M : ι → FrobeniusModule.{u, v} K) (v : (pi M).carrier) (i : ι) :
    (pi M).frobenius v i = (M i).frobenius (v i) :=
  rfl

/-- An eigenvalue of the Frobenius of a finite direct sum is an eigenvalue of the Frobenius of
one of the summands: a nonzero eigenvector has a nonzero component. -/
theorem exists_hasEigenvalue_of_hasEigenvalue_pi {M : ι → FrobeniusModule.{u, v} K} {α : K}
    (hα : (pi M).frobeniusEnd.HasEigenvalue α) : ∃ i, (M i).frobeniusEnd.HasEigenvalue α := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hv
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv.2
  refine ⟨i, Module.End.hasEigenvalue_of_hasEigenvector (x := v i) ?_⟩
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  exact ⟨congrFun hv.1 i, hi⟩

/-- A finite direct sum of Frobenius modules pure of weight `w` is pure of weight `w`. -/
theorem IsPureOfWeight.pi {ι' : K →+* ℂ} {q : ℕ} {M : ι → FrobeniusModule.{u, v} K} {w : ℝ}
    (h : ∀ i, (M i).IsPureOfWeight ι' q w) : (pi M).IsPureOfWeight ι' q w := fun α hα ↦
  have ⟨i, hi⟩ := exists_hasEigenvalue_of_hasEigenvalue_pi hα
  h i α hi

end Pi

section Induced

variable (M : FrobeniusModule.{u, v} K) (e : ℕ)

/-- The block-cyclic Frobenius `(v₀, …, v_{e-1}) ↦ (F v_{e-1}, v₀, …, v_{e-2})` on `M^e`. -/
noncomputable def inducedFrobenius : (Fin e → M.carrier) ≃ₗ[K] (Fin e → M.carrier) where
  toFun v i := if h : (i : ℕ) = 0 then M.frobenius (v ⟨e - 1, by omega⟩) else v ⟨i - 1, by omega⟩
  invFun v i := if h : (i : ℕ) = e - 1 then M.frobenius.symm (v ⟨0, by omega⟩)
    else v ⟨i + 1, by omega⟩
  map_add' v w := by
    funext i
    by_cases h : (i : ℕ) = 0 <;> simp [h]
  map_smul' c v := by
    funext i
    by_cases h : (i : ℕ) = 0 <;> simp [h]
  left_inv v := by
    funext i
    by_cases h : (i : ℕ) = e - 1
    · have hv : v ⟨e - 1, by omega⟩ = v i := congrArg v (Fin.ext h.symm)
      simp [h, hv]
    · simp [h]
  right_inv v := by
    funext i
    by_cases h : (i : ℕ) = 0
    · have hv : v ⟨0, by omega⟩ = v i := congrArg v (Fin.ext h.symm)
      simp [h, hv]
    · have : (i : ℕ) - 1 ≠ e - 1 := by omega
      simp [h, this, Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]

/-- The Frobenius cycle `M^e` of length `e` through `M`: `e` copies of `M`, with the
block-cyclic Frobenius `(v₀, …, v_{e-1}) ↦ (F v_{e-1}, v₀, …, v_{e-2})` whose `e`-th power is
the Frobenius of `M` on every copy. -/
noncomputable def induced : FrobeniusModule.{u, v} K where
  carrier := Fin e → M.carrier
  frobenius := M.inducedFrobenius e

variable {M e}

lemma induced_frobenius_apply_zero (v : (M.induced e).carrier) (i : Fin e) (hi : (i : ℕ) = 0) :
    (M.induced e).frobenius v i = M.frobenius (v ⟨e - 1, by omega⟩) :=
  dif_pos hi

lemma induced_frobenius_apply_of_ne_zero (v : (M.induced e).carrier) (i : Fin e)
    (hi : (i : ℕ) ≠ 0) : (M.induced e).frobenius v i = v ⟨i - 1, by omega⟩ :=
  dif_neg hi

/-- If `λ` is an eigenvalue of the block-cyclic Frobenius of the cycle `M^e`, then `λ ^ e` is an
eigenvalue of the Frobenius of `M`: an eigenvector `v` satisfies `vₖ = λ^{e-1-k} v_{e-1}`, so
`v_{e-1} ≠ 0` and `F v_{e-1} = λ v₀ = λ^e v_{e-1}`. -/
theorem hasEigenvalue_pow_of_hasEigenvalue_induced {α : K}
    (hα : (M.induced e).frobeniusEnd.HasEigenvalue α) : M.frobeniusEnd.HasEigenvalue (α ^ e) := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hv
  obtain ⟨hv, hv0⟩ := hv
  have hv' (i : Fin e) : (M.induced e).frobenius v i = α • v i := congrFun hv i
  have he : 0 < e := by
    obtain ⟨i, -⟩ := Function.ne_iff.1 hv0
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  -- `v_{e-1-n} = α ^ n • v_{e-1}`
  have hpow (n : ℕ) (hn : n < e) : v ⟨e - 1 - n, by omega⟩ = α ^ n • v ⟨e - 1, by omega⟩ := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hv' ⟨e - 1 - n, by omega⟩
      rw [induced_frobenius_apply_of_ne_zero _ _ (by simp; omega)] at h
      rw [pow_succ', mul_smul, ← ih (by omega), ← h]
      exact congrArg v (Fin.ext (by simp; omega))
  have hlast : v ⟨e - 1, by omega⟩ ≠ 0 := by
    intro h0
    refine hv0 (funext fun i ↦ ?_)
    have := hpow (e - 1 - i) (by omega)
    rw [h0, smul_zero] at this
    rw [Pi.zero_apply, ← this]
    exact congrArg v (Fin.ext (by simp; omega))
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v ⟨e - 1, by omega⟩) ?_
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  refine ⟨?_, hlast⟩
  have h := hv' ⟨0, he⟩
  rw [induced_frobenius_apply_zero _ _ rfl] at h
  have h0 := hpow (e - 1) (by omega)
  have h0' : v ⟨0, he⟩ = α ^ (e - 1) • v ⟨e - 1, by omega⟩ := by
    rw [← h0]
    exact congrArg v (Fin.ext (by simp))
  change M.frobenius _ = _
  rw [h, h0', smul_smul, ← pow_succ', Nat.sub_add_cancel he]

/-- **Purity of a Frobenius cycle.** If `M` is `ι`-pure of weight `w` relative to `q ^ e`, then
the cycle `M^e` is `ι`-pure of weight `w` relative to `q`: for an eigenvalue `λ` of its
Frobenius, `λ ^ e` is an eigenvalue of the Frobenius of `M`, so
`|ι λ| ^ e = (q ^ e) ^ (w / 2) = (q ^ (w / 2)) ^ e`. -/
theorem IsPureOfWeight.induced {ι : K →+* ℂ} {q : ℕ} {w : ℝ}
    (h : M.IsPureOfWeight ι (q ^ e) w) : (M.induced e).IsPureOfWeight ι q w := by
  intro α hα
  have hb := h _ (hasEigenvalue_pow_of_hasEigenvalue_induced hα)
  have he : e ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
    exact hv.2 (funext fun i ↦ i.elim0)
  have e' : ((q : ℝ) ^ e) ^ (w / 2) = ((q : ℝ) ^ (w / 2)) ^ e := by
    rw [← Real.rpow_natCast ((q : ℝ) ^ (w / 2)) e, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast (q : ℝ) e, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  rw [map_pow, norm_pow, Nat.cast_pow, e'] at hb
  exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) he).1 hb

end Induced

end FrobeniusModule
