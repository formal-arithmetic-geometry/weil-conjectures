/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.AddChar

/-!
# Sums of additive characters

An additive character `ψ` of a finite group which takes, at some point `b`, a value with
`ψ(b) - 1` a unit sums to zero. Unlike `AddChar.sum_eq_zero_of_ne_one`, this holds for an
arbitrary commutative target ring.

## Main statements

- `AddChar.sum_eq_zero_of_isUnit_sub_one`: `∑_a ψ(a) = 0` if `ψ(b) - 1` is a unit.
-/

@[expose] public section

namespace AddChar

variable {A R : Type*} [AddGroup A] [Fintype A] [CommRing R]

/-- If `ψ(b) - 1` is a unit for some `b`, then the sum of the values of the additive character
`ψ` vanishes: translation by `b` shows `ψ(b) ∑_a ψ(a) = ∑_a ψ(a)`. -/
theorem sum_eq_zero_of_isUnit_sub_one {ψ : AddChar A R} {b : A} (hb : IsUnit (ψ b - 1)) :
    ∑ a, ψ a = 0 := by
  have hS : ψ b * ∑ a, ψ a = ∑ a, ψ a := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.addLeft b) _ _ fun a ↦ by
      rw [Equiv.coe_addLeft, map_add_eq_mul]
  exact hb.mul_left_cancel (by rw [sub_mul, hS, one_mul, sub_self, mul_zero])

end AddChar
