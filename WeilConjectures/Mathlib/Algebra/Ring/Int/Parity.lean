/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Tactic.Linarith

/-!
# The triangular numbers `m(m ± 1) / 2` as integers

For every integer `m`, the product `m * (m + 1)` of two consecutive integers is even, so the
integer division `m * (m + 1) / 2` is an honest half. This file records that fact in the two
forms `m * (m + 1) / 2` and `m * (m - 1) / 2`, together with the two identities about them that
a second-order recursion over `ℤ` with these exponents needs:

* their second differences are constant equal to `1`;
* they add up to `m ^ 2`.
-/

@[expose] public section

namespace Int

/-- Twice the triangular number `m(m+1)/2` is `m(m+1)`: the product of two consecutive integers
is even. -/
theorem two_mul_mul_add_one_ediv_two (m : ℤ) : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
  Int.mul_ediv_cancel' (two_dvd_mul_add_one m)

/-- Twice the triangular number `m(m-1)/2` is `m(m-1)`: the product of two consecutive integers
is even. -/
theorem two_mul_mul_sub_one_ediv_two (m : ℤ) : 2 * (m * (m - 1) / 2) = m * (m - 1) := by
  have h := two_mul_mul_add_one_ediv_two (m - 1)
  rwa [sub_add_cancel, mul_comm (m - 1) m] at h

/-- **The second difference of `m ↦ m(m+1)/2` is `1`.** -/
theorem mul_add_one_ediv_two_add (m : ℤ) :
    (m + 1) * (m + 1 + 1) / 2 + (m - 1) * (m - 1 + 1) / 2 =
      m * (m + 1) / 2 + m * (m + 1) / 2 + 1 := by
  linarith [two_mul_mul_add_one_ediv_two (m + 1), two_mul_mul_add_one_ediv_two (m - 1),
    two_mul_mul_add_one_ediv_two m]

/-- **The second difference of `m ↦ m(m-1)/2` is `1`.** -/
theorem mul_sub_one_ediv_two_add (m : ℤ) :
    (m + 1) * (m + 1 - 1) / 2 + (m - 1) * (m - 1 - 1) / 2 =
      m * (m - 1) / 2 + m * (m - 1) / 2 + 1 := by
  linarith [two_mul_mul_sub_one_ediv_two (m + 1), two_mul_mul_sub_one_ediv_two (m - 1),
    two_mul_mul_sub_one_ediv_two m]

/-- **The two triangular numbers attached to `m` add up to `m ^ 2`.** -/
theorem mul_add_one_ediv_two_add_mul_sub_one_ediv_two (m : ℤ) :
    m * (m + 1) / 2 + m * (m - 1) / 2 = m ^ 2 := by
  linarith [two_mul_mul_add_one_ediv_two m, two_mul_mul_sub_one_ediv_two m]

end Int
