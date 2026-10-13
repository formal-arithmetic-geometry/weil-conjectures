/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Blueprint statements

def-weil-pbc-symmetric-product-morphism.
-/

@[expose] public section

namespace AlgebraicGeometry

/-- def-weil-pbc-symmetric-product-morphism. -/
noncomputable def symmetricProductPolynomial (n : ℕ) (_hn : 0 < n) (j : Fin (n + 1)) :
    MvPolynomial (Fin n ⊕ Fin n) ℤ :=
  (∏ i : Fin n,
    (Polynomial.C (MvPolynomial.X (Sum.inl i)) * Polynomial.X +
      Polynomial.C (MvPolynomial.X (Sum.inr i)) :
      Polynomial (MvPolynomial (Fin n ⊕ Fin n) ℤ))).coeff j

end AlgebraicGeometry
