/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleWeilFundamentalRepresentation

/-! # Point and path independence for scalar descent on the constant unit

Source: Weil II (1.1.1) b)-d), (1.1.6), and the constant-line normalization in
`def-wf-constant-weil-twist`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Scalar normalization of a descent map on the constant unit holds at every fibre.
Source: Weil II (1.1.1) b)-d), (1.1.6), and the constant-line normalization in
literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-r-real-linear/
def-wf-constant-weil-twist.md.
(blueprint: lem-wf-etale-constant-unit-frobenius-transport).

Proof: the constant-section identifications identify every integral unit fibre with
the inverse limit of the constant coefficient quotients. For a path, naturality for
the section maps from the terminal cover shows that its finite germ map is the
identity in these coordinates. Apply the limit projections and then extend scalars
to the finite coefficient field and to Q. Thus both the path map and the
pullback-fibre comparison respect the constant coordinates used for descent.
A rational morphism between the two constant rank-one systems is locally a scalar.
On a common finite coefficient field this follows by clearing denominators and
reducing the integral matrix at all quotient levels; the compatible matrices are
locally constant, and connectedness makes their value constant on Y. The coefficient
localization preserves this description on a common finite extension. Consequently
one descent isomorphism has the same scalar in the constant coordinates at every
geometric point. These coordinates use the same coefficient module Q for points
with different algebraically closed residue fields as well: the constant-section
stalk comparison is defined separately at each point, and finite-path naturality
fixes these sections. No common residue-field extension is required. The hypothesis
identifies this common scalar
with b at the first fibre, giving the asserted equality at the second fibre. This
assertion concerns an already given descent map and makes no existence claim. -/
theorem etaleConstantUnitFrobenius_transport
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [ConnectedSpace Y] [IsNoetherian Y]
    [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (h : Y ≅ Y) (b : Qˣ)
    (theta : (lisseAlgebraicAutomorphismPullback h l Q).obj
      (lisseAlgebraicUnit l Y Q) ≅ lisseAlgebraicUnit l Y Q)
    {κ : Type u} [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ Y)
    (path : FiniteEtale.fiber t ≅ FiniteEtale.fiber (t ≫ h.hom))
    (ht : (etaleWeilFrobenius l Q h t path
      (Endofunctor.IsoAlgebra.mk (lisseAlgebraicUnit l Y Q) theta)).toLinearMap =
        (b : Q) • LinearMap.id)
    {κ' : Type u} [Field κ'] [IsAlgClosed κ'] (t' : Spec (.of κ') ⟶ Y)
    (path' : FiniteEtale.fiber t' ≅ FiniteEtale.fiber (t' ≫ h.hom)) :
    (etaleWeilFrobenius l Q h t' path'
      (Endofunctor.IsoAlgebra.mk (lisseAlgebraicUnit l Y Q) theta)).toLinearMap =
        (b : Q) • LinearMap.id := by sorry

end AlgebraicGeometry.Scheme
