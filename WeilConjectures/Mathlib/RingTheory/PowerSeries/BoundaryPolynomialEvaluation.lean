/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Analysis.Analytic.ConvergenceRadius
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Polynomial evaluation excludes boundary cancellation

If polynomials `B, N, D` and a power series `L` over `ℂ` satisfy `B N = D L`, and `L` converges
absolutely at `z` with nonzero sum while `D(z) ≠ 0`, then `B(z) ≠ 0`.

## Main statements

- `PowerSeries.boundary_polynomial_ne_zero`
-/

@[expose] public section
set_option autoImplicit false

namespace PowerSeries

private theorem polynomial_mul_evaluation (L : PowerSeries ℂ) (P : Polynomial ℂ) (z : ℂ)
    (hL : Summable fun n : ℕ ↦ ‖coeff n L * z ^ n‖) :
    (∑' n : ℕ, coeff n ((P : PowerSeries ℂ) * L) * z ^ n) =
      P.eval z * ∑' n : ℕ, coeff n L * z ^ n := by
  have hP : Summable fun n : ℕ ↦ ‖P.coeff n * z ^ n‖ :=
    summable_of_ne_finset_zero (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simpa [Nat.lt_succ_iff] using hn), zero_mul, norm_zero]
  have hPe : (∑' n : ℕ, P.coeff n * z ^ n) = P.eval z := by
    rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simpa [Nat.lt_succ_iff] using hn), zero_mul], Polynomial.eval_eq_sum_range]
  rw [← hPe, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hP hL]
  apply tsum_congr
  intro n
  rw [coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.mem_antidiagonal.mp hp, pow_add, Polynomial.coeff_coe]
  ring

/-- Let `B, N, D` be complex polynomials and `L` a complex power series with `B N = D L`. If `L`
converges absolutely at `z` with nonzero sum and `D(z) ≠ 0`, then `B(z) ≠ 0`. -/
theorem boundary_polynomial_ne_zero
    (B N D : Polynomial ℂ) (L : PowerSeries ℂ) (z : ℂ)
    (hidentity : (B * N : Polynomial ℂ) = (D : PowerSeries ℂ) * L)
    (hL : Summable fun n : ℕ ↦ ‖coeff n L * z ^ n‖)
    (hD : D.eval z ≠ 0) (hsum : (∑' n : ℕ, coeff n L * z ^ n) ≠ 0) :
    B.eval z ≠ 0 := by
  have hsumPoly (P : Polynomial ℂ) :
      (∑' n : ℕ, coeff n (P : PowerSeries ℂ) * z ^ n) = P.eval z := by
    simp only [Polynomial.coeff_coe]
    rw [tsum_eq_sum (s := Finset.range (P.natDegree + 1)) fun n hn ↦ by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (by simpa [Nat.lt_succ_iff] using hn), zero_mul], Polynomial.eval_eq_sum_range]
  have hev := congrArg (fun S : PowerSeries ℂ ↦ ∑' n : ℕ, coeff n S * z ^ n) hidentity
  rw [hsumPoly, Polynomial.eval_mul, polynomial_mul_evaluation L D z hL] at hev
  intro hB
  rw [hB, zero_mul] at hev
  exact mul_ne_zero hD hsum hev.symm

end PowerSeries
