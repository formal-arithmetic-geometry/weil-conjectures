/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Reverse

/-!
# Reversing a product of linear factors

The reverse of the monic linear polynomial `X - a` is `1 - a * X`; consequently the reverse of a
product `∏ (X - aᵢ)` is `∏ (1 - aᵢ * X)`.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [CommRing R]

@[simp]
theorem reverse_X_sub_C (a : R) : (X - C a).reverse = 1 - C a * X := by
  nontriviality R
  have h1 : (1 : R[X]).reverse = 1 := by simpa using reverse_C (1 : R)
  have hX : (X : R[X]).reverse = 1 := by simpa [h1] using reverse_mul_X (1 : R[X])
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg, sub_eq_add_neg,
    neg_mul]

/-- The reverse of a product of monic linear factors `∏ (X - a)` is `∏ (1 - a * X)`. -/
theorem reverse_multiset_prod_X_sub_C [NoZeroDivisors R] (s : Multiset R) :
    ((s.map fun a ↦ X - C a).prod).reverse = (s.map fun a ↦ 1 - C a * X).prod := by
  induction s using Multiset.induction with
  | empty => simpa using reverse_C (1 : R)
  | cons a s ih => simp [ih]

end Polynomial
