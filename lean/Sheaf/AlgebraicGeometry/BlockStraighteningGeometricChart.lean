/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Sheaf.AlgebraicGeometry.BlockStraighteningData
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.FiniteType

/-! # Auxiliary step of block straightening -/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory
namespace AlgebraicGeometry.HilbertCoefficient

/-- Construct the common affine coefficient chart and all its geometric identities,
after the initial Jacobian calculation. No projection operator is part of this step.
Source: BM 1997 (9.8)(a)--(d), Remarks 9.9--9.11, pp.279--280;
steps 2--6 of the stored block proof
(blueprint: lem-trf-block-straightening-geometric-chart).

Proof: apply the implicit Taylor calculus to h=blockEquations on the Jacobian open.
The given derivations agree with those supplied there: their difference is a
k-derivation vanishing on all coordinates, hence zero on an etale chart. The zero
scheme has the w etale chart and at every point its graph substitution straightens
the equation ideal. Taylor uniqueness identifies the original expansions after
extension to that point's residue field. Replacing y by phi(W)+Y preserves the
first exponent: it cannot lower degree, and every changed term of equal degree
is later in lexicographic order. The inverse has the same property. Transport
membership and generation through this isomorphism. Define rho by the regular
iterated y derivatives divided by factorials and restricted to the zero scheme;
the multi-index Leibniz formula proves additivity, multiplicativity and the unit
identity. The implicit coefficient formula proves specialization and the displayed
coefficient identities. Old tests remain zero coefficientwise after derivation and
restriction. Old derivative equations stay in (T), and new ones vanish at Y=T=0.
The full transverse Jacobian is block triangular; shrink by its determinant,
nonzero at the center. Choose an affine neighborhood of the center inside this
open. Since the zero scheme is closed in the Jacobian open, its affine open is
closed in a further ambient open, giving the pullback square. All identities
restrict to this common neighborhood. It is affine of finite type over k, so its
global ring is a finitely generated k-algebra, and is Noetherian. The inclusion
is a closed immersion followed by an open immersion, so its residue maps are
isomorphisms and the center residue map is surjective. For r=0 use an
affine neighborhood in the original chart, with no new equation or substitution. -/
theorem blockStraighteningGeometricChart {k : Type u} [Field k] [CharZero k]
    (B : Scheme.{u}) {m r t s : ℕ}
    (c : MvPolynomial (Fin m ⊕ Fin r) k →+* Γ(B, ⊤)) (a : B)
    (D : ImplicitCoordinateDerivations B c)
    (α : Fin s → Fin ((m + r) + t) →₀ ℕ) (d Q : ℕ)
    (f : Fin s → MvPowerSeries (Fin t) Γ(B, ⊤))
    (pick : Fin (r + t) → Fin s) (β : Fin (r + t) → Fin ((m + r) + t) →₀ ℕ)
    (A : BlockStraighteningInput B c a D α d Q f pick β)
    (hzero : ∀ j : Fin r, B.Γevaluation a (blockEquations D f pick β j) = 0)
    (hjac : B.Γevaluation a (implicitJacobian D (blockEquations D f pick β)) ≠ 0) :
    ∃ G : BlockStraighteningGeometry A, IsNoetherianRing Γ(G.open_in_zero.toScheme, ⊤) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
