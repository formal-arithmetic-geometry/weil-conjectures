/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleConstantUnitScalarAction

/-! # Lifting a scalar fibre map to the constant etale-adic unit

Source: Weil II (1.1.1) b)-d), (1.1.6), and the constant-line construction in
`def-wf-constant-weil-twist`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A prescribed nonzero scalar at one geometric fibre lifts to descent on the unit.
Source: Weil II (1.1.1) b)-d), (1.1.6), and the constant-line construction in
literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-r-real-linear/
def-wf-constant-weil-twist.md.
(blueprint: lem-wf-etale-constant-unit-frobenius-lift).

Proof: at a finite coefficient field, the integral unit is the tower of constant
quotient module sheaves. Pullback along h reindexes this tower. The constant-sheaf
pullback comparison, normalized on constant sections, gives a levelwise isomorphism
from its pullback to itself. Naturality in the quotient module makes these maps
commute with reduction. They therefore give an integral lisse isomorphism. Rationalize
and include its base coefficient model into the algebraic coefficient localization.
Choose a finite coefficient extension containing b and rescale this map there by b;
its inverse is the original inverse followed by multiplication by b inverse. This
uses rational maps and requires no stable integral lattice for b.
On the chosen fibre, a finite path fixes a constant section by naturality for its map
from the terminal cover. The finite germ formula for etaleFinitePathIso, followed by
inverse-limit projections and the two scalar extensions, therefore shows that the
canonical descent isomorphism has degree-one operator the identity. Linearity of the
same scalar extensions shows that the rescaled isomorphism has operator b times the
identity. This is existence at the specified point and path only; independence of the
point and path and uniqueness of descent are separate assertions. -/
theorem etaleConstantUnitFrobenius_lift
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [ConnectedSpace Y] [IsNoetherian Y]
    [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (h : Y ≅ Y) (b : Qˣ)
    {κ : Type u} [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ Y)
    (path : FiniteEtale.fiber t ≅ FiniteEtale.fiber (t ≫ h.hom)) :
    ∃ theta : (lisseAlgebraicAutomorphismPullback h l Q).obj
        (lisseAlgebraicUnit l Y Q) ≅ lisseAlgebraicUnit l Y Q,
      (etaleWeilFrobenius l Q h t path
        (Endofunctor.IsoAlgebra.mk (lisseAlgebraicUnit l Y Q) theta)).toLinearMap =
          (b : Q) • LinearMap.id := by
  obtain ⟨theta₁, htheta₁⟩ := etaleConstantUnitFrobenius_one l Y Q h t path
  obtain ⟨theta, htheta⟩ := etaleConstantUnit_scalar_action l Y Q h b t path theta₁
  refine ⟨theta, ?_⟩
  rw [htheta, htheta₁]

end AlgebraicGeometry.Scheme
