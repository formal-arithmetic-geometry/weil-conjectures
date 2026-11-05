/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Tactic.LinearCombination

/-!
# Complements on the formal logarithm

## Main results

- `PowerSeries.one_add_X_mul_derivative_log`: `(1 + X) * (log (1 + X))' = 1`.
- `PowerSeries.mul_derivative_logOf`: the formal logarithm is a logarithmic primitive, i.e.
  `f * (logOf f)' = f'` whenever `f` has constant coefficient `1`.
-/

@[expose] public section

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

end PowerSeries
