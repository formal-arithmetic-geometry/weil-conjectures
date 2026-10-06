/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Normalized polynomials over an algebraically closed field

Over an algebraically closed field, a polynomial with constant coefficient `1` is determined by
its multiset of roots: it is the product of the `X - a` over its roots, rescaled by the unique
constant making the constant coefficient `1`.

If the roots of two such polynomials `P` and `Q` correspond under `z ↦ (c z)⁻¹`, then `P`
and `Q` are reciprocal to each other, `P (c⁻¹ t⁻¹) = t ^ (-deg P) · (lc Q)⁻¹ · Q (t)`, and
their leading coefficients satisfy `lc P · lc Q = c ^ deg P`. For the Frobenius factors of a variety
over a finite field these are the reciprocity relations deduced from Poincaré duality.

## Main statements

- `Polynomial.eq_of_coeff_zero_eq_one_of_roots_eq`: a normalized polynomial is determined by its
  roots.
- `Polynomial.eval_inv_mul_inv_of_roots_eq_map_inv`: reciprocity of normalized polynomials.
- `Polynomial.leadingCoeff_mul_leadingCoeff_of_roots_eq_map_inv`: the product rule for their
  leading coefficients.
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

section Reciprocity

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- Over an algebraically closed field, a polynomial with constant coefficient `1` has leading
coefficient the inverse of `∏ (-z)` over its roots `z`. -/
theorem leadingCoeff_mul_prod_roots_neg {P : K[X]} (hP : P.coeff 0 = 1) :
    P.leadingCoeff * (P.roots.map fun z ↦ -z).prod = 1 := by
  have := (IsAlgClosed.splits P).eval_eq_prod_roots 0
  rw [← coeff_zero_eq_eval_zero, hP] at this
  simpa only [zero_sub] using this.symm

omit [IsAlgClosed K] in
/-- The roots of a polynomial with constant coefficient `1` are nonzero. -/
theorem ne_zero_of_mem_roots_of_coeff_zero_eq_one {P : K[X]} (hP : P.coeff 0 = 1) {z : K}
    (hz : z ∈ P.roots) : z ≠ 0 := by
  rintro rfl
  have := (mem_roots'.1 hz).2
  rw [IsRoot, ← coeff_zero_eq_eval_zero, hP] at this
  exact one_ne_zero this

/-- **The determinant product rule.** If the roots of `Q` are the `(c z)⁻¹` for the roots `z` of
`P`, both normalized by constant coefficient `1`, then the leading coefficients satisfy
`lc P · lc Q = c ^ deg P`. -/
theorem leadingCoeff_mul_leadingCoeff_of_roots_eq_map_inv {P Q : K[X]} (hP : P.coeff 0 = 1)
    (hQ : Q.coeff 0 = 1) {c : K} (hc : c ≠ 0)
    (h : Q.roots = P.roots.map fun z ↦ (c * z)⁻¹) :
    P.leadingCoeff * Q.leadingCoeff = c ^ P.natDegree := by
  have h1 := leadingCoeff_mul_prod_roots_neg hP
  have h2 := leadingCoeff_mul_prod_roots_neg hQ
  rw [h, Multiset.map_map] at h2
  set R := (P.roots.map ((fun z ↦ -z) ∘ fun z ↦ (c * z)⁻¹)).prod with hR
  have key : (P.roots.map fun z ↦ -z).prod * R = (c⁻¹) ^ P.natDegree := by
    rw [hR, ← Multiset.prod_map_mul]
    rw [Multiset.map_congr rfl (g := fun _ ↦ c⁻¹) fun z hz ↦ by
      have := ne_zero_of_mem_roots_of_coeff_zero_eq_one hP hz
      simp only [Function.comp_apply]
      field_simp]
    rw [Multiset.map_const', Multiset.prod_replicate,
      ← splits_iff_card_roots.1 (IsAlgClosed.splits P)]
  have : P.leadingCoeff * Q.leadingCoeff * c⁻¹ ^ P.natDegree = 1 := by
    rw [← key]
    linear_combination (Q.leadingCoeff * R) * h1 + h2
  rw [inv_pow] at this
  field_simp at this
  exact this

/-- **Reciprocity of normalized polynomials.** If the roots of `Q` are the `(c z)⁻¹` for the
roots `z` of `P`, both normalized by constant coefficient `1`, then
`P (c⁻¹ t⁻¹) = t ^ (-deg P) · (lc Q)⁻¹ · Q (t)` for every `t ≠ 0`. -/
theorem eval_inv_mul_inv_of_roots_eq_map_inv {P Q : K[X]} (hP : P.coeff 0 = 1)
    (hQ : Q.coeff 0 = 1) {c : K} (hc : c ≠ 0)
    (h : Q.roots = P.roots.map fun z ↦ (c * z)⁻¹) {t : K} (ht : t ≠ 0) :
    P.eval (c⁻¹ * t⁻¹) = t ^ (-(P.natDegree : ℤ)) * Q.leadingCoeff⁻¹ * Q.eval t := by
  have hQ0 : Q.leadingCoeff ≠ 0 := by
    rw [Ne, leadingCoeff_eq_zero]
    rintro rfl
    simp at hQ
  rw [(IsAlgClosed.splits P).eval_eq_prod_roots, (IsAlgClosed.splits Q).eval_eq_prod_roots, h,
    Multiset.map_map]
  rw [Multiset.map_congr rfl (g := fun z ↦ -z * (t⁻¹ * (t - (c * z)⁻¹))) fun z hz ↦ by
      have := ne_zero_of_mem_roots_of_coeff_zero_eq_one hP hz
      field_simp
      ring]
  rw [Multiset.prod_map_mul, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    splits_iff_card_roots.1 (IsAlgClosed.splits P), zpow_neg, zpow_natCast, inv_pow,
    mul_assoc, inv_mul_cancel_left₀ hQ0]
  simp only [Function.comp_def]
  linear_combination ((t ^ P.natDegree)⁻¹ * (P.roots.map fun z ↦ t - (c * z)⁻¹).prod) *
    leadingCoeff_mul_prod_roots_neg hP

end Reciprocity

end Polynomial
