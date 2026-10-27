/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U8
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientDivisionData

/-! # Nonvanishing of the restricted division determinants

Source: Bierstone--Milman, Invent. Math. 128 (1997), Lemma 7.7 and completion of Theorem 9.6, p.282.
(blueprint: lem-trf-coefficient-first-exponent-determinants)
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonomialDiagram

namespace AlgebraicGeometry.HilbertCoefficient

open Classical in
/-- First exponents give nonzero restricted determinants in every degree.

Source: BM 1997, Lemma 7.7, pp.263--264, and Theorem 9.6, p.282
(blueprint: lem-trf-coefficient-first-exponent-determinants).

Proof: Assign each division index its vertex plus multiplier, or its remainder
exponent. Choose the least vertex dividing a diagram exponent. This gives a
bijection with the degree-t monomials, including empty vertex lists. Restriction
to essential variables preserves the ordered distinct vertices and their degrees.
The coefficient at an earlier restricted exponent vanishes: extend that exponent
by zero to all Z variables and then all W variables and apply the first-exponent
hypothesis. At the vertex itself the coefficient is the nonzero constant Taylor
coefficient. Multiplying by the column monomial preserves the degree-lex order.
Consequently, after ordering rows and columns by assigned exponents, the matrix
is triangular with diagonal entries ev(c_i,alpha_i), or 1 for a remainder.
The coefficient homomorphism carries the regular coefficient matrix to this
matrix, and carries its determinant to its determinant. The triangular determinant
is the product of these nonzero entries in a field, hence is nonzero. -/
theorem coefficient_first_exponent_determinants
    {A L : Type u} [CommRing A] [Field L] {m n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (D : Set (Fin n →₀ ℕ))
    (hα : IsOrderedVertexFamily D α)
    (c : Fin s → (Fin n →₀ ℕ) → A)
    (ev : A →+* L) (T : A →+* MvPowerSeries (Fin m) L)
    (hconst : ∀ r : A, MvPowerSeries.constantCoeff (T r) = ev r)
    (hfirst : ∀ i : Fin s,
      MvPowerSeries.coeff (fullVertex m (α i)) (coefficientFamilySeries T c i) ≠ 0 ∧
      ∀ e : (Fin m ⊕ Fin n) →₀ ℕ,
        Finsupp.DegLex (fun x y : Fin m ⊕ Fin n ↦ Sum.Lex (· < ·) (· < ·) x y) (· < ·)
          e (fullVertex m (α i)) →
        MvPowerSeries.coeff e (coefficientFamilySeries T c i) = 0) :
    ∀ q t : ℕ, ev (Matrix.det
      (coefficientDivisionMatrix (essentialVertices (prefixVertices α q))
        (restrictedCoefficientForms α c q) t)) ≠ 0 := by sorry

end AlgebraicGeometry.HilbertCoefficient
