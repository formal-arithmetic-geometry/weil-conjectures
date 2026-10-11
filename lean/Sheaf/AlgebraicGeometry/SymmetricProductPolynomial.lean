/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Symmetric-product coordinate polynomials

Source: Stacks Project, Etale Cohomology, proof of Lemma 59.91.10 (Tag 0A4F);
the Weil conjectures blueprint, `sec-proper-base-change`, `sk-thm-reduction`
(blueprint: def-weil-pbc-symmetric-product-morphism).
-/

@[expose] public section

namespace AlgebraicGeometry

/-- For `n ≥ 1`, the coefficient `F_j` of `t^j` in
`∏ i, (x_i * t + y_i)`, with integer coefficients. The variables are indexed by
`Fin n ⊕ Fin n`, the left summand for `x_i` and the right summand for `y_i`.
The `j`-th coefficient is the sum over `j`-element subsets `J` of the products
`∏ i ∈ J, x_i * ∏ i ∉ J, y_i`; hence `F_0 = ∏ y_i`, `F_n = ∏ x_i`, and every
monomial has degree one in each pair. Evaluation in any commutative ring gives
the corresponding coefficient of the product of linear forms. The later
symmetric-product morphism uses these polynomials as homogeneous coordinates.
Stacks Tag 0A4F uses the reverse indexing `(F_0 * t^n + ⋯ + F_n)`.
(blueprint: def-weil-pbc-symmetric-product-morphism) -/
noncomputable def symmetricProductPolynomial (n : ℕ) (_hn : 0 < n) (j : Fin (n + 1)) :
    MvPolynomial (Fin n ⊕ Fin n) ℤ :=
  (∏ i : Fin n,
    (Polynomial.C (MvPolynomial.X (Sum.inl i)) * Polynomial.X +
      Polynomial.C (MvPolynomial.X (Sum.inr i)) :
      Polynomial (MvPolynomial (Fin n ⊕ Fin n) ℤ))).coeff j

end AlgebraicGeometry
