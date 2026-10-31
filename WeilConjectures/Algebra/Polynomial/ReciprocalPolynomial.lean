/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Field.Defs

import Mathlib.Data.Int.Cast.Lemmas

/-!
# Reciprocal polynomials with constant coefficient one

Source: the Weil conjectures blueprint, `sec-zeta-weil/sk-thm-rh/prop-arithmetic-roots.md`,
the reciprocal-polynomial display and reciprocal-root convention
(blueprint: lem-weil-reciprocal-polynomial).

The reciprocal polynomial is Mathlib's `Polynomial.reverse`: its coefficient in degree
`j ≤ P.natDegree` is `P.coeff (P.natDegree - j)`, and its higher coefficients vanish.
Thus it is precisely the finite sum defining `P^#` in the source. We write `P.natDegree`
for `r` and `P.leadingCoeff` for `c_r`, without introducing another definition.
-/

@[expose] public section

universe u v

namespace Polynomial

/-- Reciprocal-polynomial properties over a commutative ring, and after coefficientwise
extension to any field in which the leading coefficient remains nonzero.

Source: the Weil conjectures blueprint, `sec-zeta-weil/sk-thm-rh/prop-arithmetic-roots.md`,
the display defining `P_i^#`, its monicity, and the reciprocal-root convention
(blueprint: lem-weil-reciprocal-polynomial).

Proof plan (the six steps of the DAG node):
1. Use `coeff_reverse` to identify the coefficient of degree `j ≤ r` with `c_(r-j)`;
   coefficients above `r` vanish. Here `r = P.natDegree`.
2. The nonzero leading coefficient excludes the zero ring. Since `c_0 = 1`, the
   trailing degree is zero. Apply `reverse_natDegree`, `reverse_leadingCoeff` and
   `trailingCoeff_eq_coeff_zero` for monicity and degree; `coeff_zero_reverse` gives
   the value at zero. These steps use the polynomial-ring and coefficient definitions.
3. Under coefficientwise extension, the surviving leading coefficient gives degree `r`
   by `natDegree_map_of_leadingCoeff_ne_zero`; `coeff_map` gives constant coefficient one.
   This uses the coefficientwise-extension and field definitions. Injective maps satisfy
   the survival hypothesis; for integers in characteristic zero, use `Int.cast_injective`
   (lem-weil-integers-injective-char-zero).
4. Apply `reflect_map` at `r` and the degree equality from step 3 to show that extension
   commutes with reversal; only survival of the leading coefficient is required.
5. For a nonzero field element, rewrite `eval₂_reverse_mul_pow` with its inverse to
   obtain the evaluation identity. At zero, use `coeff_zero_reverse` and `coeff_map`.
   This uses the root, field and coefficientwise-extension definitions.
6. The value at zero is nonzero, and away from zero the factor `x^r` is nonzero.
   The identity in step 5 therefore gives the root equivalence. Ordinary roots are
   nonzero because the constant coefficient is one; inversion is an involution on
   nonzero field elements, so the equivalence identifies exactly the inverse roots.
-/
theorem reciprocal_polynomial_of_constantCoeff_one {R : Type u} [CommRing R] (P : R[X])
    (h0 : P.coeff 0 = 1) (hr : P.leadingCoeff ≠ 0) :
    P.reverse.Monic ∧
      P.reverse.natDegree = P.natDegree ∧
      P.reverse.eval 0 = P.leadingCoeff ∧
      ∀ (K : Type v) [Field K] (φ : R →+* K), φ P.leadingCoeff ≠ 0 →
        (P.map φ).natDegree = P.natDegree ∧
          (P.map φ).eval 0 = 1 ∧
          P.reverse.map φ = (P.map φ).reverse ∧
          (∀ x : K, (P.reverse.map φ).IsRoot x ↔
            x ≠ 0 ∧ (P.map φ).IsRoot x⁻¹) ∧
          (∀ x : K, x ≠ 0 →
            (P.reverse.map φ).eval x = x ^ P.natDegree * (P.map φ).eval x⁻¹) ∧
          (P.reverse.map φ).eval 0 = φ P.leadingCoeff ∧
          (P.reverse.map φ).eval 0 ≠ 0 := by
  sorry

end Polynomial
