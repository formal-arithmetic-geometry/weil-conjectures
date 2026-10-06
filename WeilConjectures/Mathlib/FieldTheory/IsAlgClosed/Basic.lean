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

The fraction field of the integral closure of a ring in an algebraically closed field is again
algebraically closed (`IsFractionRing.isAlgClosed_integralClosure`).
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

open Polynomial in
/-- The fraction field of the integral closure of a ring `R` in an algebraically closed field
`K` is algebraically closed: a root `y ∈ K` of a polynomial over it has an integral multiple
`c • y` with `c ≠ 0` in the integral closure, so `y = (c • y) / c` lies in the fraction field. -/
theorem IsFractionRing.isAlgClosed_integralClosure {R K L : Type*} [CommRing R] [Field K]
    [IsAlgClosed K] [Algebra R K] [Field L] [Algebra (integralClosure R K) L]
    [IsFractionRing (integralClosure R K) L] : IsAlgClosed L := by
  have hinj : Function.Injective (algebraMap (integralClosure R K) K) := Subtype.val_injective
  let : Algebra L K := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower (integralClosure R K) L K := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsFractionRing.lift_algebraMap hinj x).symm
  refine IsAlgClosed.of_exists_root L fun p hmon hirr ↦ ?_
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_aeval_eq_zero K p (degree_pos_of_irreducible hirr).ne'
  have halg : IsAlgebraic (integralClosure R K) y :=
    (IsFractionRing.isAlgebraic_iff _ L K).2 ⟨p, hmon.ne_zero, hy⟩
  obtain ⟨c, hc0, hint⟩ := halg.exists_integral_multiple
  let b : integralClosure R K := ⟨c • y, isIntegral_trans _ hint⟩
  have hc : algebraMap (integralClosure R K) K c ≠ 0 := (map_ne_zero_iff _ hinj).2 hc0
  have hb : algebraMap (integralClosure R K) K b = algebraMap (integralClosure R K) K c * y :=
    rfl
  refine ⟨algebraMap (integralClosure R K) L b / algebraMap (integralClosure R K) L c,
    (algebraMap L K).injective ?_⟩
  rw [← coe_aeval_eq_eval, ← aeval_algebraMap_apply, map_zero, map_div₀,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, hb,
    mul_div_cancel_left₀ _ hc]
  exact hy
