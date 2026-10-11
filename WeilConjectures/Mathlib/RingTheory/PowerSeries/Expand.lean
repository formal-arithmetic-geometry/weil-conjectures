/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Derivatives of expanded power series

The Euler operator `X d/dX` commutes with the expansion `X ↦ X ^ p` up to the factor `p`:
`X (f (X ^ p))' = p (X f')(X ^ p)`.
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

end PowerSeries
