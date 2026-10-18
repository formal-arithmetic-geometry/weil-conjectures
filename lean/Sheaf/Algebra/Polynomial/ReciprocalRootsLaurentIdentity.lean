/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Laurent
public import WeilConjectures.Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.Algebra.Polynomial.ReciprocalRootFactorization

/-!
# Laurent reciprocity for normalized polynomials

Source: the blueprint of the Weil conjectures, `prop-duality-reciprocity`, proof steps 2--3
(blueprint: lem-weil-reciprocal-roots-laurent-identity).

## Main statement

- `Polynomial.reciprocal_roots_laurent_identity`: normalized polynomials whose reciprocal
  root multisets are related by scaling satisfy the determinant and Laurent reciprocity identities.
-/

@[expose] public section

universe u

open Polynomial
open scoped BigOperators

namespace Polynomial

/-- If two normalized polynomials have reciprocal-root factorizations related by
`α ↦ c / α`, their determinant constants multiply to `c ^ n` and they satisfy the corresponding
Laurent-polynomial reciprocity identity and its evaluation form. The Laurent substitution is written
coefficientwise as the finite sum obtained from `P(c⁻¹ T⁻¹)`.

Source: the blueprint of the Weil conjectures, `prop-duality-reciprocity`, proof steps 2--3
(blueprint: lem-weil-reciprocal-roots-laurent-identity). The proof follows the factorization into
linear factors, computes the two leading coefficients and then multiplies the factorwise Laurent
identity; evaluation at a nonzero field element gives the final clause. -/
theorem reciprocal_roots_laurent_identity {L : Type u} [Field L] [IsAlgClosed L]
    (P Q : L[X]) (hP0 : P.coeff 0 = 1) (hQ0 : Q.coeff 0 = 1)
    (α : Fin P.natDegree → Lˣ)
    (hP : P = ∏ j, (1 - C (α j : L) * X))
    (c : L) (hc : c ≠ 0)
    (hQ : Q = ∏ j, (1 - C (c * (α j : L)⁻¹) * X)) :
    Q.natDegree = P.natDegree ∧
      (-1 : L) ^ P.natDegree * P.coeff P.natDegree ≠ 0 ∧
      (-1 : L) ^ Q.natDegree * Q.coeff Q.natDegree ≠ 0 ∧
      ((-1 : L) ^ P.natDegree * P.coeff P.natDegree) *
          ((-1 : L) ^ Q.natDegree * Q.coeff Q.natDegree) = c ^ P.natDegree ∧
      (∑ k ∈ P.support,
          LaurentPolynomial.C (P.coeff k * c⁻¹ ^ k) *
            LaurentPolynomial.T (-(k : ℤ))) =
        LaurentPolynomial.C ((-1 : L) ^ P.natDegree) *
          LaurentPolynomial.T (-(P.natDegree : ℤ)) *
            LaurentPolynomial.C
              ((-1 : L) ^ Q.natDegree * Q.coeff Q.natDegree)⁻¹ *
              Polynomial.toLaurent Q ∧
      ∀ t : L, t ≠ 0 →
        P.eval (c⁻¹ * t⁻¹) =
          t ^ (-(P.natDegree : ℤ)) *
            (Q.coeff P.natDegree)⁻¹ * Q.eval t := by
  sorry

end Polynomial
