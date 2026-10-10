/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.FieldSimp

/-!
# Complements on forward differences

A function `f : ℕ → G` is a "polynomial of degree `< n`" when its `n`-th forward difference
vanishes. We show that this property can be detected through forward differences with two coprime
steps, and that an integer valued function with vanishing `n`-th forward difference is given by a
rational polynomial of degree `< n`.

## Main results

- `fwdDiff_iter_fwdDiff`: forward differences with different steps commute.
- `fwdDiff_iter_succ_eq_zero_of_coprime`: if `Δ_[A] f` and `Δ_[B] f` have vanishing `n`-th
  forward difference for coprime `A` and `B`, then `f` has vanishing `(n + 1)`-st forward
  difference.
- `exists_polynomial_of_fwdDiff_iter_eq_zero`: an integer valued function on `ℕ` whose `n`-th
  forward difference vanishes is given by a rational polynomial of degree `< n`.
-/

@[expose] public section

open Finset Function Polynomial

open scoped fwdDiff

open fwdDiff_aux

variable {M G : Type*} [AddCommMonoid M] [AddCommGroup G]

/-- Forward differences with different steps commute. -/
lemma fwdDiff_iter_fwdDiff (h k : M) (f : M → G) (n : ℕ) (y : M) :
    Δ_[h]^[n] (Δ_[k] f) y = Δ_[k] (Δ_[h]^[n] f) y := by
  have : Δ_[k] f = (fun r ↦ f (r + k)) - f := rfl
  rw [this, ← coe_fwdDiffₗ_pow, map_sub, coe_fwdDiffₗ_pow, Pi.sub_apply,
    fwdDiff_iter_comp_add]
  rfl

/-- If the `n`-th forward differences of `Δ_[A] f` and `Δ_[B] f` vanish for coprime `A` and `B`,
then the `(n + 1)`-st forward difference of `f` vanishes: the `n`-th forward difference of `f` is
periodic with periods `A` and `B`, hence constant. -/
theorem fwdDiff_iter_succ_eq_zero_of_coprime (f : ℕ → G) {A B : ℕ} (hAB : Nat.Coprime A B)
    {n : ℕ} (hA : ∀ m, Δ_[1]^[n] (Δ_[A] f) m = 0) (hB : ∀ m, Δ_[1]^[n] (Δ_[B] f) m = 0)
    (m : ℕ) : Δ_[1]^[n + 1] f m = 0 := by
  set g := Δ_[1]^[n] f
  have hgA (m : ℕ) : g (m + A) = g m := by
    have := hA m
    rw [fwdDiff_iter_fwdDiff, fwdDiff, sub_eq_zero] at this
    exact this
  have hgB (m : ℕ) : g (m + B) = g m := by
    have := hB m
    rw [fwdDiff_iter_fwdDiff, fwdDiff, sub_eq_zero] at this
    exact this
  have hgA' (m k : ℕ) : g (m + k * A) = g m := by
    induction k with
    | zero => simp
    | succ k ih => rw [add_mul, one_mul, ← add_assoc, hgA, ih]
  have hgB' (m k : ℕ) : g (m + k * B) = g m := by
    induction k with
    | zero => simp
    | succ k ih => rw [add_mul, one_mul, ← add_assoc, hgB, ih]
  rw [iterate_succ_apply', fwdDiff, sub_eq_zero]
  rcases Nat.lt_or_ge 1 B with hB1 | hB1
  · obtain ⟨x, -, hx⟩ := Nat.exists_mul_mod_eq_one_of_coprime hAB hB1
    rw [mul_comm] at hx
    have hx' : x * A = x * A / B * B + 1 := by
      rw [← hx]
      exact (Nat.div_add_mod' _ _).symm
    change g (m + 1) = g m
    rw [← hgB' (m + 1) (x * A / B), add_assoc, add_comm 1, ← hx', hgA']
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hB1 with rfl | rfl
    · rw [Nat.coprime_zero_right] at hAB
      subst hAB
      simpa using hgA m
    · exact hgB m

/-- **An integer valued function with vanishing `n`-th forward difference is a polynomial of
degree `< n`**, by the Gregory–Newton formula `f m = ∑_{k < n} (m choose k) Δ^k f 0`. -/
theorem exists_polynomial_of_fwdDiff_iter_eq_zero (f : ℕ → ℤ) {n : ℕ}
    (hf : ∀ m, Δ_[1]^[n] f m = 0) :
    ∃ P : ℚ[X], P.degree < n ∧ ∀ m : ℕ, P.eval (m : ℚ) = f m := by
  have hzero (k : ℕ) (hk : n ≤ k) : Δ_[1]^[k] f 0 = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_comm, iterate_add_apply]
    have : Δ_[1]^[n] f = 0 := funext hf
    rw [this]
    have h0 (j : ℕ) : Δ_[1]^[j] (0 : ℕ → ℤ) = 0 := by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [iterate_succ_apply', ih]
        rfl
    rw [h0]
    rfl
  refine ⟨∑ k ∈ range n, C (((Δ_[1]^[k] f 0 : ℤ) : ℚ) / k.factorial) * descPochhammer ℚ k, ?_, ?_⟩
  · refine (degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr fun k hk ↦ ?_
    refine (degree_mul_le _ _).trans_lt ?_
    refine (add_le_add degree_C_le (degree_le_natDegree.trans_eq
      (congrArg _ (descPochhammer_natDegree ℚ k)))).trans_lt ?_
    rw [zero_add]
    exact WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk)
  · intro m
    have h := shift_eq_sum_fwdDiff_iter 1 f m 0
    rw [zero_add, smul_eq_mul, mul_one] at h
    rw [h, Polynomial.eval_finsetSum]
    push_cast
    have key (k : ℕ) : (m.choose k • Δ_[1]^[k] f 0 : ℤ) =
        (C (((Δ_[1]^[k] f 0 : ℤ) : ℚ) / k.factorial) * descPochhammer ℚ k).eval (m : ℚ) := by
      rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial, nsmul_eq_mul,
        Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      field_simp
    simp_rw [key]
    have hsub : ∀ s t : Finset ℕ, (∀ k ∈ t, k ∉ s → n ≤ k ∨ m < k) → s ⊆ t →
        ∑ k ∈ t, (C (((Δ_[1]^[k] f 0 : ℤ) : ℚ) / k.factorial) * descPochhammer ℚ k).eval (m : ℚ) =
          ∑ k ∈ s, (C (((Δ_[1]^[k] f 0 : ℤ) : ℚ) / k.factorial) * descPochhammer ℚ k).eval
            (m : ℚ) := by
      intro s t hst hs
      refine (Finset.sum_subset hs fun k hkt hks ↦ ?_).symm
      rw [eval_mul, eval_C, descPochhammer_eval_eq_descFactorial]
      rcases hst k hkt hks with hk | hk
      · rw [hzero k hk]
        simp
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hk]
        simp
    rw [hsub (range n ∩ range (m + 1)) (range (m + 1)) (fun k _ hk ↦ by
        simp only [Finset.mem_inter, Finset.mem_range, not_and_or, not_lt] at hk ⊢
        omega) Finset.inter_subset_right,
      hsub (range n ∩ range (m + 1)) (range n) (fun k _ hk ↦ by
        simp only [Finset.mem_inter, Finset.mem_range, not_and_or, not_lt] at hk ⊢
        omega) Finset.inter_subset_left]
