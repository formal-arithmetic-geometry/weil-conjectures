/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RegularHilbertCoefficientDatum

/-! # Invariance of formal jet length under coefficient field extension

Source: Bierstone--Milman, Invent. Math. 128 (1997), Remark 3.8 and the finite-jet
field-extension argument in the proof of Theorem 9.4.
(blueprint: lem-trf-formal-jet-length-scalar-extension).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v

namespace AlgebraicGeometry.HilbertCoefficient

/-- Every finite formal jet has the same length after coefficient field extension.
This holds for arbitrary ideals, without division or Jacobian hypotheses.

Source: BM 1997, Remark 3.8 and proof of Theorem 9.4, p.278; Remark 3.8, p.234.
(blueprint: lem-trf-formal-jet-length-scalar-extension).

Proof: Modulo the (q+1)-st power of the variable ideal, the monomials of total degree
at most q form a finite basis. The image of K is a subspace of this finite-dimensional
space. Choose a basis of that subspace and lift its finitely many elements to K.
In the target truncated series ring the image of the extended ideal is precisely the
scalar extension of this subspace: multiplication by a target series uses only its
finite polynomial truncation, and source monomial multiples of elements of K remain
in K. Extend the chosen subspace basis to a monomial-space basis. Its determinant is
nonzero and stays nonzero under the field embedding, so the quotient dimensions agree.
In each quotient the variable ideal is nilpotent and its residue field is the coefficient
field (unless the quotient is zero). Filter by its powers: each successive quotient is
annihilated by the maximal ideal, so its ring-module length is its vector-space dimension.
Additivity along this finite filtration identifies total length with quotient dimension.
Thus the two displayed lengths agree. The zero quotient, zero variables, q=0, and zero
or unit ideals are included. -/
theorem formal_jet_length_scalar_extension
    {L : Type u} [Field L] {E : Type v} [Field E] (ι : L →+* E)
    {σ : Type} [Finite σ] (K : Ideal (MvPowerSeries σ L)) (q : ℕ) :
    extendedHilbert (K.map (MvPowerSeries.map ι)) q = extendedHilbert K q := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
