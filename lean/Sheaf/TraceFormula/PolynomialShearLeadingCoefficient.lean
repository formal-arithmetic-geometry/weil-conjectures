module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Fin.SuccPred

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open scoped BigOperators

namespace Algebra

/--
Triangular polynomial substitution with a nonzero scalar leading coefficient.

Source: Stacks Project, Algebra, Tags 051N (`lemma-helper-polynomial`) and
051M (`lemma-helper`), finite-support and dominant-weight argument
(blueprint: lem-trf-polynomial-shear-leading-coefficient).

The proof writes the polynomial as a finite sum of monomials, chooses base-power
weights separating its finite support, expands the substitution monomial by
monomial, and groups all terms below the unique maximal weight.  It uses only
the polynomial-ring finite-support and evaluation operations represented by
`MvPolynomial`, and elementary integer inequalities; the coefficient `a` is
one of the original nonzero coefficients, so no cancellation or division in
`R` is used.  When `m = 0`, the exponent family is empty and the substitution
is the identity on the single variable.
-/
theorem exists_polynomial_shear_leading_coefficient
    (R : Type u) [CommRing R] (m : ℕ)
    (g : MvPolynomial (Fin (m + 1)) R)
    (hg : ¬ ∃ r : R, g = MvPolynomial.C r) :
    ∃ (e : Fin m → ℕ) (d : ℕ) (a : R)
      (b : Fin d → MvPolynomial (Fin m) R),
      (∀ i, 0 < e i) ∧
        0 < d ∧
          (∃ ν : (Fin (m + 1) →₀ ℕ),
            MvPolynomial.coeff ν g = a ∧ a ≠ 0) ∧
            MvPolynomial.aeval (R := R)
                (fun i : Fin (m + 1) ↦
                  if h : i ≠ Fin.last m then
                    (MvPolynomial.X (Fin.castSucc (i.castPred h)) : MvPolynomial (Fin (m + 1)) R) +
                      (MvPolynomial.X (Fin.last m) :
                        MvPolynomial (Fin (m + 1)) R) ^ (e (i.castPred h))
                  else (MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) R)) g =
              (MvPolynomial.C a : MvPolynomial (Fin (m + 1)) R) *
                (MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) R) ^ d +
                ∑ j : Fin d,
                  MvPolynomial.rename Fin.castSucc (b j) *
                    (MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) R) ^ (j : ℕ) := by
  sorry

end Algebra
