/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Tactic.LinearCombination

/-!
# Complements on polynomial identities

## Main results

- `Polynomial.eq_or_sub_dvd_derivative_eval_of_isRoot` — two roots `a ≠ b` of a polynomial `f`
  over a domain satisfy `a - b ∣ f'(a)`.
-/

@[expose] public section

open Polynomial

/-- **Two roots of a polynomial over a domain are equal or close**: if `a` and `b` are roots of
`f`, then `a = b` or `a - b` divides `f'(a)`. -/
theorem Polynomial.eq_or_sub_dvd_derivative_eval_of_isRoot {R : Type*} [CommRing R] [IsDomain R]
    {f : R[X]} {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b) :
    a = b ∨ a - b ∣ f.derivative.eval a := by
  by_cases hab : a = b
  · exact Or.inl hab
  refine Or.inr ?_
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f a (b - a)
  have hk' : (f.derivative.eval a + k * (b - a)) * (b - a) = 0 := by
    rw [add_sub_cancel] at hk
    rw [IsRoot.def] at ha hb
    linear_combination hb - ha - hk
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h0 := (mul_eq_zero.mp hk').resolve_right hba
  refine ⟨k, ?_⟩
  linear_combination h0
