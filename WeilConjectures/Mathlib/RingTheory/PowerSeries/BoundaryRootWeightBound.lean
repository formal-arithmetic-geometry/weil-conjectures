/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A root-free boundary polynomial bounds logarithmic weights

If a complex polynomial `B` divisible by `1 - α T^d` has no zero on the disc of radius
`q^{-(a/2 + 1)}`, then the Frobenius weight of `α` with respect to `q^d` is at most `a + 2`.

## Main statements

- `PowerSeries.boundary_weight_le_add_two_of_no_zero`
-/

@[expose] public section
set_option autoImplicit false

open AlgebraicGeometry

namespace PowerSeries

/-- Let `α ≠ 0` and let `B` be a complex polynomial divisible by `1 - ι(α) T^d` with no zero on
the open disc of radius `q^{-(a/2 + 1)}`. Then the Frobenius weight of `α` with respect to `q^d`
is at most `a + 2`. -/
theorem boundary_weight_le_add_two_of_no_zero
    {E : Type*} [Field E] (ι : E →+* ℂ) (q d : ℕ) (hq : 1 < q) (hd : 0 < d)
    (α : E) (hα : α ≠ 0) (a : ℝ) (B : Polynomial ℂ)
    (hfactor : 1 - Polynomial.C (ι α) * Polynomial.X ^ d ∣ B)
    (hdisc : ∀ z : ℂ, ‖z‖ < (q : ℝ) ^ (-(a / 2 + 1)) → B.eval z ≠ 0) :
    WeilGroup.frobeniusWeight ι (q ^ d) α ≤ a + 2 := by
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq'
  have hia : ι α ≠ 0 := (map_ne_zero ι).2 hα
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (ι α)⁻¹ hd
  have hlocal : (1 - Polynomial.C (ι α) * Polynomial.X ^ d).eval z = 0 := by
    simp [hz, mul_inv_cancel₀ hia]
  have hB : B.eval z = 0 := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hfactor hlocal
  have hR : (q : ℝ) ^ (-(a / 2 + 1)) ≤ ‖z‖ := by
    by_contra! hlt
    exact hdisc z hlt hB
  have hlogR := Real.log_le_log (Real.rpow_pos_of_pos hq0 _) hR
  rw [Real.log_rpow hq0] at hlogR
  have hnorm : ‖z‖ ^ d = ‖ι α‖⁻¹ := by rw [← norm_pow, hz, norm_inv]
  have hlog := congrArg Real.log hnorm
  rw [Real.log_pow, Real.log_inv] at hlog
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogq : Real.log ((q ^ d : ℕ) : ℝ) = (d : ℝ) * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
  have hscaled := mul_le_mul_of_nonneg_left hlogR hd'.le
  unfold WeilGroup.frobeniusWeight
  rw [hlogq, div_le_iff₀ (mul_pos hd' (Real.log_pos hq'))]
  nlinarith

end PowerSeries
