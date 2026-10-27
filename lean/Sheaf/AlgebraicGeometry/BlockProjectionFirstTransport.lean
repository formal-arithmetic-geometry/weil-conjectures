/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Sheaf.AlgebraicGeometry.BlockStraighteningData

/-! # Auxiliary step of block straightening -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory
namespace AlgebraicGeometry.HilbertCoefficient

/-- Conjugation by the implicit graph transports the initial-exponent property
of an arbitrary stored operator at the distinguished center.
Source: BM 1997 Remark 9.11 and the conjugacy calculation in step 7 of the stored
block proof (blueprint: lem-trf-block-projection-first-transport).

Proof: the residue-field map of the closed immersion at the center is an
isomorphism. Taylor uniqueness identifies the ambient coefficient map with the
base extension of tau, followed by the graph automorphism. The graph and its
inverse preserve every first exponent: replacement by a zero-constant W series
cannot decrease degree, and at equal degree strictly raises the lexicographic
exponent. The pure Y term has unchanged coefficient. Coefficient extraction in
T commutes with both substitutions, so they preserve the set of monomials
passing the tests. Induction on the finite operator syntax gives conjugacy:
all stored scalars, columns, sums and matrix entries are transported, while
extraction and insertion indices stay fixed. Apply the original first-exponent
property to the inverse-transformed input and then substitute forward. For no
y variables the substitutions are identities; empty tests impose no restriction. -/
theorem blockProjectionFirstTransport {k : Type u} [Field k] [CharZero k]
    {B C : Scheme.{u}} {m r t s : ℕ}
    {c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)}
    {h : Fin r → Γ(B, ⊤)} {D : ImplicitCoordinateDerivations B c}
    (j : C ⟶ B) (center : C) (a : B) (ha : j center = a)
    (hres : Function.Surjective (j.residueFieldMap center).hom)
    (points : ∀ b : C, ImplicitTaylorPoint.{u, u} c h D j b)
    (τ : Γ(B, ⊤) →+* MvPowerSeries (Fin m ⊕ Fin r) (B.residueField a))
    (hτ : isTaylorMap c (B.Γevaluation a).hom τ)
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d Q : ℕ)
    (P : MvPowerSeries.FiniteCoefficientExpression Γ(B, ⊤) t 1 t 1)
    (hP : blockPreservesFirst α d Q P τ) :
    blockPreservesFirst α d Q P (blockPointCoefficientMap (points center)) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
