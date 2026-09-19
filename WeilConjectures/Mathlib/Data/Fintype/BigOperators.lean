/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# Products and sums along a `Pi.single` exponent vector

A product `∏ i, f i ^ c i` of integer powers over a finite index type collapses to a single
factor when the exponent vector `c` is concentrated at one index, and likewise for a sum
`∑ i, c i • f i` of integer multiples.

## Main results

* `Fintype.prod_zpow_pi_single`: `∏ i, f i ^ (Pi.single j n) i = f j ^ n`.
* `Fintype.sum_zsmul_pi_single`: `∑ i, (Pi.single j n) i • f i = n • f j`.
-/

@[expose] public section

namespace Fintype

variable {ι G : Type*} [Fintype ι] [DecidableEq ι]

/-- A product of integer powers whose exponent vector is concentrated at `j` is the `j`-th
factor. -/
theorem prod_zpow_pi_single [DivisionCommMonoid G] (f : ι → G) (j : ι) (n : ℤ) :
    ∏ i, f i ^ (Pi.single j n : ι → ℤ) i = f j ^ n := by
  rw [Fintype.prod_eq_single j fun i hi ↦ by rw [Pi.single_eq_of_ne hi, zpow_zero],
    Pi.single_eq_same]

/-- A sum of integer multiples whose coefficient vector is concentrated at `j` is the `j`-th
summand. -/
theorem sum_zsmul_pi_single [SubtractionCommMonoid G] (f : ι → G) (j : ι) (n : ℤ) :
    ∑ i, (Pi.single j n : ι → ℤ) i • f i = n • f j := by
  rw [Fintype.sum_eq_single j fun i hi ↦ by rw [Pi.single_eq_of_ne hi, zero_zsmul],
    Pi.single_eq_same]

end Fintype
