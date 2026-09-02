/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# A normalized polynomial over an algebraically closed field is its root multiset

Over an algebraically closed field, a polynomial with constant coefficient `1` is determined by
its multiset of roots: it is the product of the `X - a` over its roots, rescaled by the unique
constant making the constant coefficient `1`.
-/

@[expose] public section

namespace Polynomial

/-- Over an algebraically closed field, a polynomial with constant coefficient `1` is determined
by its multiset of roots. -/
theorem eq_of_coeff_zero_eq_one_of_roots_eq {K : Type*} [Field K] [IsAlgClosed K] {P Q : K[X]}
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) (h : P.roots = Q.roots) : P = Q := by
  set m : K[X] := (P.roots.map fun a => X - C a).prod with hm
  have hPm : C P.leadingCoeff * m = P :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C (splits_iff_card_roots.1 (IsAlgClosed.splits P))
  have hQm : C Q.leadingCoeff * m = Q := by
    rw [hm, h]
    exact C_leadingCoeff_mul_prod_multiset_X_sub_C (splits_iff_card_roots.1 (IsAlgClosed.splits Q))
  have hPc : P.leadingCoeff * m.coeff 0 = 1 := by
    have h1 := congrArg (fun p => Polynomial.coeff p 0) hPm
    simpa [hP] using h1
  have hQc : Q.leadingCoeff * m.coeff 0 = 1 := by
    have h1 := congrArg (fun p => Polynomial.coeff p 0) hQm
    simpa [hQ] using h1
  have hm0 : m.coeff 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hPc
    exact zero_ne_one hPc
  have : P.leadingCoeff = Q.leadingCoeff := mul_right_cancel₀ hm0 (hPc.trans hQc.symm)
  rw [← hPm, ← hQm, this]

end Polynomial
