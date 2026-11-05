/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coefficients of a product of power series

## Main statements

- `PowerSeries.coeff_mul_eq_sum_range`: the coefficient of `X ^ n` in `φ * ψ` is
  `∑_{i = 0}^{n} cᵢ(φ) c_{n - i}(ψ)`.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommSemiring R]

end PowerSeries
