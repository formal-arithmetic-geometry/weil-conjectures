/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Sheaf.RingTheory.FormalInitialDiagram
public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-! # Homogeneous division from prescribed first exponents

Source: BM 1997, (7.1), (7.2)(1)--(2), and Lemma 7.7; the unitriangular
argument in step 5 of the generic monotone diagram construction.
(blueprint: lem-trf-initial-exponent-homogeneous-division)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MonomialDiagram

/-- Every finite family with prescribed first exponents gives unique homogeneous
supported division by its initial forms. No monotonicity or vertex hypothesis is needed.

Source: BM 1997, (7.1), (7.2)(1)--(2), and Lemma 7.7; step 5 of
lem-trf-generic-monotone-diagram.
(blueprint: lem-trf-initial-exponent-homogeneous-division).

Proof: fix a degree t and partition its finitely many monomials by the first orthant
containing them, with the others assigned to the remainder. Subtracting a vertex
identifies its part with the quotient indices in DivisionIndex. The corresponding
column is T^b times the initial homogeneous form, or the remainder monomial.
All its monomials have degree t. Its least exponent is its assigned exponent and its
coefficient is the nonzero first coefficient of the divisor. Thus the matrix of the
indexed columns in the ordered degree-t monomial basis is triangular with nonzero
diagonal. Back substitution makes it an invertible linear map. Every homogeneous
polynomial therefore has unique finite coefficients in the indexed family. If no
vertex divides a degree-t exponent all columns are remainder monomials. Duplicate
vertices simply give empty later quotient regions. This also covers the empty family,
zero variables, and degrees below a divisor's degree. -/
theorem initialExponentHomogeneousDivision {L : Type u} [Field L] {n : ℕ}
    {ι : Type} [Finite ι] [LinearOrder ι]
    (G : ι → MvPowerSeries (Fin n) L) (α : ι → Fin n →₀ ℕ)
    (hα : ∀ i : ι, IsFirstExponent (G i) (α i)) (t : ℕ) :
    HasUniqueDivision (generated α) α
      (fun i ↦ MvPowerSeries.truncTotal ((α i).degree + 1)
        (MvPowerSeries.homogeneousComponent (α i).degree (G i))) t := by
  sorry

end MonomialDiagram
