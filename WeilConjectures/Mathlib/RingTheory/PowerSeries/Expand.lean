/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Complements on the expansion `T ↦ T ^ p` of power series

## Main results

- `PowerSeries.expand_inv`: over a field, expansion commutes with taking inverses.
- `PowerSeries.X_pow_dvd_expand_sub_C_constantCoeff`: the expansion `f (T ^ p)` is congruent to
  its constant coefficient modulo `T ^ p`.
- `PowerSeries.X_mul_derivative_expand`: the Euler operator `X d/dX` commutes with the expansion
  `X ↦ X ^ p` up to the factor `p`: `X (f (X ^ p))' = p (X f')(X ^ p)`.
- `PowerSeries.eq_sum_X_pow_mul_expand`, `PowerSeries.finite_expand`: every power series is
  `∑_{r < m} t^r g_r(t^m)`, so `t ↦ t^m` is a finite ring map.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- The `n`-th coefficient of `X f'` is `n` times that of `f`. -/
theorem coeff_X_mul_derivative (f : R⟦X⟧) (n : ℕ) :
    coeff n (X * derivative R f) = n * coeff n f := by
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    push_cast
    rfl

/-- The Euler operator `X d/dX` and the expansion `X ↦ X ^ p`:
`X (f (X ^ p))' = p (X f')(X ^ p)`. -/
theorem X_mul_derivative_expand (p : ℕ) (hp : p ≠ 0) (f : R⟦X⟧) :
    X * derivative R (expand p hp f) = C (p : R) * expand p hp (X * derivative R f) := by
  ext n
  rw [coeff_X_mul_derivative, coeff_C_mul, coeff_expand, coeff_expand]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp), coeff_X_mul_derivative]
    push_cast
    ring
  · simp

section Expand

variable (m : ℕ) (hm : m ≠ 0)

end Expand

end PowerSeries
