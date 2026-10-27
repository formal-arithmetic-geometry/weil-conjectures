/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Positive products and radii of convergence

Source: literature/blueprint/master/blueprint/sec-purity-real-sheaves/sk-p-real-rankin/
lem-rp-positive-product-radius.md,
node lem-rp-positive-product-radius (blueprint: lem-rp-positive-product-radius).
-/

@[expose] public section

open scoped ENNReal NNReal BigOperators ComplexOrder

namespace PowerSeries

universe u

/--
Source: literature/blueprint/master/blueprint/sec-purity-real-sheaves/sk-p-real-rankin/
lem-rp-positive-product-radius.md, node lem-rp-positive-product-radius
(blueprint: lem-rp-positive-product-radius).

For a degreewise locally finite family of nonnegative power series with constant term one,
if its coefficientwise product is the Taylor series at zero of a function holomorphic on the
open disc of radius `R`, each factor has radius at least `R`.  The proof compares every factor
coefficient with the corresponding nonnegative product coefficient, applies Taylor convergence
and the nonnegative summability comparison. The source library's
`eval_ne_zero_of_lt_radius_inv` proves the final zero-free assertion by evaluating the
absolutely convergent Cauchy product of a polynomial with its inverse.

Proof:
1. Write the constant coefficient of every factor as one. In degree `n`, local finiteness
   supplies a finite set of factors. If `j` belongs to this set, the term selecting degree
   `n` from `j` and degree zero from all other factors is its coefficient. All other terms
   are nonnegative. If `j` is absent and `n > 0`, its coefficient is zero by local finiteness;
   degree zero follows from the constant terms. Thus `0 ≤ a_{j,n} ≤ A_n`, and `A_0 = 1`.
2. Apply `lem-rp-taylor-sum-on-disc` (`Complex.hasSum_taylorSeries_on_eball`) at zero
   and at every real `0 ≤ t < R`. The Taylor coefficients are `A_n`. Taking real parts
   gives summability of the nonnegative real series with terms `A_n * t^n`.
3. Apply `lem-rp-nonnegative-summable-comparison` (`Summable.of_nonneg_of_le`) to
   `0 ≤ a_{j,n} * t^n ≤ A_n * t^n`. Thus each factor converges absolutely for every
   `0 ≤ t < R`; the radius definition of `d-real-series` gives the first conclusion.
   For `R = ∞` use all finite `t`; for `R = 0` the conclusion is automatic.
4. If `f j = P⁻¹`, apply the already proved source-library theorem
   `PowerSeries.eval_ne_zero_of_lt_radius_inv`. The condition `P(0) = 1` gives the required
   nonzero constant coefficient, and step 3 places the given point strictly inside the
   radius of the inverse. That theorem evaluates the absolutely convergent Cauchy product
   `P * P⁻¹ = 1`, so a zero of `P` would give `0 = 1`.
-/
theorem positive_product_radius
    {J : Type u} (f : J → ℂ⟦X⟧)
    (hf : ∀ j, (f j).HasNonnegCoeffs)
    (hconst : ∀ j, PowerSeries.constantCoeff (f j) = 1)
    (F : ℂ⟦X⟧)
    (hlocal : ∀ n : ℕ, ∃ S : Finset J,
      (∀ (j : J) (k : ℕ), 1 ≤ k → k ≤ n →
        PowerSeries.coeff k (f j) ≠ 0 → j ∈ S) ∧
      PowerSeries.coeff n F = PowerSeries.coeff n (∏ j ∈ S, f j))
    (R : ℝ≥0∞) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h (Metric.eball 0 R))
    (hTaylor : ∀ n : ℕ,
      PowerSeries.coeff n F = (Nat.factorial n : ℂ)⁻¹ * iteratedDeriv n h 0)
    : (∀ j : J, R ≤ (f j).radius) ∧
      (∀ (j : J) (P : Polynomial ℂ),
        f j = (P : ℂ⟦X⟧)⁻¹ → P.eval 0 = 1 →
          ∀ z ∈ Metric.eball 0 R, P.eval z ≠ 0) := by
  classical
  have hf' : ∀ j n, 0 ≤ coeff n (f j) := fun j ↦ hasNonnegCoeffs_iff.mp (hf j)
  have hnonneg (S : Finset J) : ∀ n, 0 ≤ coeff n (∏ j ∈ S, f j) := by
    induction S using Finset.induction_on with
    | empty => intro n; simp only [Finset.prod_empty, coeff_one]; split_ifs <;> simp
    | insert j S hj ih =>
      intro n
      rw [Finset.prod_insert hj, coeff_mul]
      exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hf' j _) (ih _)
  have hprodconst (S : Finset J) : constantCoeff (∏ j ∈ S, f j) = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun j _ ↦ hconst j
  have hF : ∀ n, 0 ≤ coeff n F := by
    intro n
    obtain ⟨S, _, hS⟩ := hlocal n
    rw [hS]
    exact hnonneg S n
  have hcoeff (j : J) (n : ℕ) : coeff n (f j) ≤ coeff n F := by
    obtain ⟨S, hS, hSF⟩ := hlocal n
    rw [hSF]
    by_cases hj : j ∈ S
    · rw [← Finset.mul_prod_erase S f hj, coeff_mul,
        ← Finset.add_sum_erase _ _
          (show ((n, 0) : ℕ × ℕ) ∈ Finset.antidiagonal n by simp)]
      simp only [coeff_zero_eq_constantCoeff_apply, hprodconst, mul_one,
        le_add_iff_nonneg_right]
      exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hf' j _) (hnonneg _ _)
    · cases n with
      | zero => simp [coeff_zero_eq_constantCoeff_apply, hconst, hprodconst]
      | succ n =>
        have hz : coeff (n + 1) (f j) = 0 := by
          by_contra hn
          exact hj (hS j (n + 1) (by omega) le_rfl hn)
        rw [hz]
        exact hnonneg S _
  have hnorm (n : ℕ) : ‖coeff n F‖ = (coeff n F).re := by
    have heq := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg (hF n))
    simpa using heq.symm
  have hRF : R ≤ F.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ le_radius_of_summable ?_
    have hz : (r : ℂ) ∈ Metric.eball 0 R := by
      simpa [Metric.mem_eball, edist_dist, Complex.norm_of_nonneg r.2] using hr
    have hs : Summable fun n ↦ coeff n F * (r : ℂ) ^ n := by
      refine (Complex.hasSum_taylorSeries_on_eball hh hz).summable.congr fun n ↦ ?_
      rw [hTaylor]
      simp only [sub_zero, smul_eq_mul]
      ring
    have hre := Complex.reCLM.summable hs
    simpa [Function.comp_def, Complex.mul_re, ← Complex.ofReal_pow, hnorm] using hre
  have hR : ∀ j, R ≤ (f j).radius := by
    intro j
    refine hRF.trans (radius_le_radius_of_norm_coeff_le fun n ↦ ?_)
    obtain ⟨a, ha, hfa⟩ := RCLike.nonneg_iff_exists_ofReal.mp (hf' j n)
    obtain ⟨b, hb, hfb⟩ := RCLike.nonneg_iff_exists_ofReal.mp (hF n)
    have hab := hcoeff j n
    rw [← hfa, ← hfb] at hab ⊢
    rw [RCLike.norm_ofReal, RCLike.norm_ofReal, abs_of_nonneg ha, abs_of_nonneg hb]
    exact_mod_cast hab
  refine ⟨hR, ?_⟩
  intro j P hfj hP z hz
  apply eval_ne_zero_of_lt_radius_inv
    (by simp [Polynomial.coeff_zero_eq_eval_zero, hP])
  rw [← hfj]
  exact (show (‖z‖₊ : ℝ≥0∞) < R by
    simpa [Metric.mem_eball, edist_dist, ← coe_nnnorm] using hz).trans_le (hR j)

end PowerSeries

end
