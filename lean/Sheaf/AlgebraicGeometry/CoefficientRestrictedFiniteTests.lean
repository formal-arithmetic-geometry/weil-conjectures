/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U8
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientDivisionData

/-! # From finite coefficient matrices to restricted division

Source: Bierstone--Milman, Invent. Math. 128 (1997), Theorem 8.1 and
completion of Theorem 9.6, p.282.
(blueprint: lem-trf-coefficient-restricted-finite-tests)
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonomialDiagram

namespace AlgebraicGeometry.HilbertCoefficient

open Classical in
/-- The bounded regular matrices suffice for every restricted degree, also after
extension of the coefficient field. No Taylor series or order locus is involved.

Source: BM 1997, Theorem 8.1, Definition 8.3, pp.273--275, and p.282
(blueprint: lem-trf-coefficient-restricted-finite-tests).

Proof: The first-dividing-vertex assignment bijects the supported family indices
with the degree-t monomials. Each restricted form is homogeneous of its vertex
degree; deleting unused variables preserves that degree. Map the square regular
matrix through ev. A nonzero determinant makes its columns a basis, hence they
span. Apply the finite-test equivalence in each prefix to propagate from the
tested degrees to unique division in every degree. For q above the maximum vertex
degree, all vertices are retained, so identify the prefix and its essential
variables with those at the maximum and use that prefix instead. This needs no
comparison between the numerical bounds of two prefixes. In each degree the
resulting basis has an inverse coefficient matrix over L. Mapping the matrix and
its inverse through j preserves both inverse identities, so the mapped family
is a basis over K. Its entries are precisely those formed from j.comp ev, because
coefficient maps commute with sums and monomials. This proves the last assertion
without requiring a stabilization bound in the universe of K. Empty monomial
index sets use the empty identity matrix. -/
theorem coefficient_restricted_finite_tests
    {A L : Type u} [CommRing A] [Field L] {n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (D : Set (Fin n →₀ ℕ))
    (hα : IsOrderedVertexFamily D α)
    (c : Fin s → (Fin n →₀ ℕ) → A) (B : ℕ → ℕ)
    (hB : ∀ q : ℕ, ∀ (R : Type u) (_ : CommRing R),
      IsFiniteDivisionTest (generated (essentialVertices (prefixVertices α q)))
        (essentialVertices (prefixVertices α q)) R (B q))
    (ev : A →+* L)
    (hdet : ∀ q t : ℕ, q ≤ Finset.univ.sup (fun i : Fin s ↦ (α i).degree) →
      t ≤ B q → ev (Matrix.det
        (coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
          (restrictedCoefficientForms α c q) t)) ≠ 0) :
    (∀ q t : ℕ, HasUniqueDivision
      (generated (essentialVertices (prefixVertices α q)))
      (essentialVertices (prefixVertices α q))
      (fun i ↦ MvPolynomial.map ev (restrictedCoefficientForms α c q i)) t) ∧
    ∀ (K : Type v) [Field K] (j : L →+* K), ∀ q t : ℕ, HasUniqueDivision
      (generated (essentialVertices (prefixVertices α q)))
      (essentialVertices (prefixVertices α q))
      (fun i ↦ MvPolynomial.map (j.comp ev) (restrictedCoefficientForms α c q i)) t := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
