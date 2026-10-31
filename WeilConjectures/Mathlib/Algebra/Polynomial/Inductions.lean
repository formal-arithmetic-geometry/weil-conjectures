/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Inductions

/-!
# Complements on `Polynomial.divX`

## Main results

- `Polynomial.eq_C_add_X_mul_C_add_X_mul` — the decomposition
  `g = g(0) + X (g'(0) + X G)` of a polynomial, with `G = divX (divX g)`.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- The decomposition `g = g(0) + X (g'(0) + X G)` of a polynomial, with `G = divX (divX g)`. -/
lemma eq_C_add_X_mul_C_add_X_mul (g : R[X]) :
    g = C (g.coeff 0) + X * (C (g.coeff 1) + X * g.divX.divX) := by
  conv_lhs => rw [← X_mul_divX_add g, ← X_mul_divX_add g.divX]
  rw [coeff_divX, add_comm _ (C (g.coeff 0)), add_comm (X * _) (C _)]

end Polynomial
