/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# An uncancelled polynomial denominator root bounds the convergence radius

Source: literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/
sk-l-dl-a1-energy/thm-wf-l2-dictionary.proof.md, final paragraph, Taylor-radius
conclusion (blueprint: lem-wf-rational-series-pole-radius).
-/

@[expose] public section

open scoped ENNReal NNReal PowerSeries

namespace PowerSeries

/-- If a formal power series over `ℂ` satisfies a polynomial fraction identity, then an
uncancelled root of the denominator bounds its convergence radius.

Source: literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/
sk-l-dl-a1-energy/thm-wf-l2-dictionary.proof.md, final paragraph, Taylor-radius
conclusion (blueprint: lem-wf-rational-series-pole-radius).
The proof assumes a radius larger than `‖a‖`, evaluates the absolutely convergent series at
`a`, and evaluates the finite Cauchy product in `Q * f = P` to obtain `P.eval a = Q.eval a * f(a)`,
contradicting `Q.eval a = 0` and `P.eval a ≠ 0`. -/
theorem radius_le_of_polynomial_mul_eq
    (P Q : Polynomial ℂ) (f : PowerSeries ℂ)
    (hQ0 : Q.coeff 0 ≠ 0) (hQf : (Q : PowerSeries ℂ) * f = (P : PowerSeries ℂ))
    {a : ℂ} (haQ : Q.eval a = 0) (haP : P.eval a ≠ 0) :
    f.radius ≤ ENNReal.ofReal ‖a‖ := by
  have _ := hQ0
  by_contra h
  have ha : (‖a‖₊ : ℝ≥0∞) < f.radius := by
    simpa only [← coe_nnnorm, ENNReal.ofReal_coe_nnreal] using lt_of_not_ge h
  have hQ : Summable fun n ↦ ‖Q.coeff n * a ^ n‖ :=
    summable_of_ne_finset_zero (s := Finset.range (Q.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
        zero_mul, norm_zero]
  have hf : Summable fun n ↦ ‖coeff n f * a ^ n‖ := by
    simpa [norm_mul, norm_pow] using summable_norm_coeff_mul_pow ha
  have hpoly (R : Polynomial ℂ) : ∑' n, R.coeff n * a ^ n = R.eval a := by
    rw [tsum_eq_sum (s := Finset.range (R.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [Nat.lt_succ_iff] using hn),
        zero_mul], Polynomial.eval_eq_sum_range]
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hQ hf
  have hcoeff (n : ℕ) :
      ∑ p ∈ Finset.antidiagonal n, Q.coeff p.1 * a ^ p.1 * (coeff p.2 f * a ^ p.2) =
        P.coeff n * a ^ n := by
    calc
      _ = coeff n ((Q : PowerSeries ℂ) * f) * a ^ n := by
        rw [coeff_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp ↦ ?_
        rw [← Finset.mem_antidiagonal.1 hp, pow_add, Polynomial.coeff_coe]
        ring
      _ = _ := by rw [hQf, Polynomial.coeff_coe]
  simp_rw [hcoeff] at key
  rw [hpoly Q, hpoly P, haQ, zero_mul] at key
  exact haP key.symm

end PowerSeries
