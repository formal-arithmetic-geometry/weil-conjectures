/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Products and sums along a `Pi.single` exponent vector

These are the `zpow` companions of `Finset.prod_pi_mulSingle'` and `Fintype.prod_pi_mulSingle'`,
whose exponent vector is the one concentrated at `j` with value `1`.

## Main results

* `Finset.prod_zpow_pi_single`: `∏ i ∈ s, f i ^ (Pi.single j n) i = f j ^ n` for `j ∈ s`, with
  its additive version `Finset.sum_zsmul_pi_single` and the two `Fintype` special cases
  `Fintype.prod_zpow_pi_single` and `Fintype.sum_zsmul_pi_single`.
-/

@[expose] public section

variable {ι G : Type*} [DecidableEq ι] [DivisionCommMonoid G]

namespace Finset

/-- A product of integer powers whose exponent vector is concentrated at `j` is the `j`-th
factor. -/
@[to_additive /-- A sum of integer multiples whose coefficient vector is concentrated at `j` is
the `j`-th summand. -/]
theorem prod_zpow_pi_single (s : Finset ι) (f : ι → G) {j : ι} (hj : j ∈ s) (n : ℤ) :
    ∏ i ∈ s, f i ^ (Pi.single j n : ι → ℤ) i = f j ^ n := by
  rw [Finset.prod_eq_single_of_mem j hj
      fun i _ hi ↦ by rw [Pi.single_eq_of_ne hi, zpow_zero],
    Pi.single_eq_same]

end Finset

namespace Fintype

variable [Fintype ι]

/-- A product of integer powers over a finite index type whose exponent vector is concentrated at
`j` is the `j`-th factor. -/
@[to_additive /-- A sum of integer multiples over a finite index type whose coefficient vector is
concentrated at `j` is the `j`-th summand. -/]
theorem prod_zpow_pi_single (f : ι → G) (j : ι) (n : ℤ) :
    ∏ i, f i ^ (Pi.single j n : ι → ℤ) i = f j ^ n :=
  Finset.prod_zpow_pi_single _ f (Finset.mem_univ j) n

end Fintype
