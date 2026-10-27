/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U8
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientDivisionData
public import Mathlib.RingTheory.MvPowerSeries.Trunc

/-! # Reindexing restricted division into all variables

Source: Bierstone--Milman, Invent. Math. 128 (1997), Lemma 7.7, pp.263--264.
(blueprint: lem-trf-coefficient-restricted-to-full)
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonomialDiagram

namespace AlgebraicGeometry.HilbertCoefficient

/-- Only the W-zero coefficients of a series are needed to compare restricted
and full supported division of its specified homogeneous forms.

Source: BM 1997, Lemma 7.7, pp.263--264, used on p.282
(blueprint: lem-trf-coefficient-restricted-to-full).

Proof: For each q, enumerate its retained vertices increasingly by Fin s_q and
its essential variables by Fin r_q. These are finite sets, including the empty
sets. Split the full variable set into those essential Z variables and their
complement, enumerate the complement, and transport exponents and polynomials
along the resulting bijection. Restriction of the degree-d_i homogeneous form
to the essential variables kills W and every other Z variable. Its coefficient
at gamma is therefore the supplied W-zero coefficient ev(c_i,gamma). The sum
of these coefficients over degree-d_i monomials is exactly the mapped restricted
form. Vertex degrees and first-vertex quotient supports are preserved by this
transport; the prefix on the full vertices is the same prefix because fullVertex
preserves degree. Distinctness follows from the ordered vertex hypothesis.
Apply hasUniqueDivision_extraVariables_iff in these finite enumerations, then
transport the unique finitely supported coefficients back. Homogeneous component
of truncTotal(d_i+1) has exactly the degree-d_i coefficients of f_i. The argument
applies to any field and does not use a Taylor order bound or a first exponent. -/
theorem coefficient_restricted_to_full
    {A : Type u} [CommRing A] {L : Type v} [Field L] {m n s : ℕ}
    (α : Fin s → Fin n →₀ ℕ) (D : Set (Fin n →₀ ℕ))
    (hα : IsOrderedVertexFamily D α)
    (c : Fin s → (Fin n →₀ ℕ) → A) (ev : A →+* L)
    (f : Fin s → MvPowerSeries (Fin m ⊕ Fin n) L)
    (hcoeff : ∀ (i : Fin s) (γ : Fin n →₀ ℕ),
      MvPowerSeries.coeff (fullVertex m γ) (f i) = ev (c i γ))
    (hdiv : ∀ q t : ℕ, HasUniqueDivision
      (generated (essentialVertices (prefixVertices α q)))
      (essentialVertices (prefixVertices α q))
      (fun i ↦ MvPolynomial.map ev (restrictedCoefficientForms α c q i)) t) :
    ∀ q t : ℕ, HasUniqueDivision
      (generated (prefixVertices (fun i ↦ fullVertex m (α i)) q))
      (prefixVertices (fun i ↦ fullVertex m (α i)) q)
      (fun i ↦ MvPolynomial.homogeneousComponent (α i.val).degree
        (MvPowerSeries.truncTotal ((α i.val).degree + 1) (f i.val))) t := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
