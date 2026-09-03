/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Complements on the formal derivative of a power series

## Main results

- `PowerSeries.map_derivative` — the formal derivative commutes with the coefficientwise map
  along a ring homomorphism.
-/

@[expose] public section

namespace PowerSeries

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The formal derivative commutes with the coefficientwise map along a ring homomorphism. -/
theorem map_derivative (φ : R →+* S) (f : R⟦X⟧) :
    map φ (derivative R f) = derivative S (map φ f) := by
  ext n
  simp [coeff_derivative]

end PowerSeries
