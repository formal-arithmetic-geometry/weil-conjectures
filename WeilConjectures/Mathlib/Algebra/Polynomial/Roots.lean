/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Complements on the roots of a polynomial

## Main results

- `Polynomial.roots_one_sub_C_mul_X`: the only root of `1 - c * X` is `c⁻¹`.
-/

@[expose] public section

namespace Polynomial

/-- The only root of `1 - c * X`, for `c ≠ 0`, is `c⁻¹`. -/
theorem roots_one_sub_C_mul_X {K : Type*} [Field K] {c : K} (hc : c ≠ 0) :
    (1 - C c * X).roots = {c⁻¹} := by
  have h : (1 - C c * X : K[X]) = C (-c) * (X - C c⁻¹) := by
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hc, C_neg, C_neg, C_1]
    ring
  rw [h, roots_C_mul _ (neg_ne_zero.2 hc), roots_X_sub_C]

end Polynomial
