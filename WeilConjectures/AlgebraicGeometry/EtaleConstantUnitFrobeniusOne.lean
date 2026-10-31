/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleWeilFundamentalRepresentation

/-! # Canonical unit descent at one fibre

Source: Weil II (1.1.1) b)-d), (1.1.6), and the constant-line construction in
`def-wf-constant-weil-twist`.

The theorem records the unscaled constant-unit comparison. Its proof is split from the
scalar rescaling and is the connected etale-adic presentation of the constant unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The constant unit has a canonical descent comparison with identity degree-one operator.
Source: Weil II (1.1.1) b)-d), (1.1.6), and
literature/blueprint/latest/blueprint/sec-purity-real-sheaves/sk-r-real-linear/
`def-wf-constant-weil-twist.md`.
(blueprint: new-t2-etale-constant-unit-frobenius-one).

Proof: identify the unit with its inverse system of constant coefficient quotients. The
pullback reindexing comparison is the identity on constant sections at each quotient,
and these maps commute with reduction. Passing to the inverse limit and then extending
scalars gives an isomorphism of the pulled-back unit with the unit. Naturality of the
finite germ maps from the terminal cover makes the induced degree-one operator the
identity after every projection and scalar extension. -/
theorem etaleConstantUnitFrobenius_one
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) [ConnectedSpace Y] [IsNoetherian Y]
    [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (h : Y ≅ Y)
    {κ : Type u} [Field κ] [IsAlgClosed κ] (t : Spec (.of κ) ⟶ Y)
    (path : FiniteEtale.fiber t ≅ FiniteEtale.fiber (t ≫ h.hom)) :
    ∃ theta : (lisseAlgebraicAutomorphismPullback h l Q).obj
        (lisseAlgebraicUnit l Y Q) ≅ lisseAlgebraicUnit l Y Q,
      (etaleWeilFrobenius l Q h t path
        (Endofunctor.IsoAlgebra.mk (lisseAlgebraicUnit l Y Q) theta)).toLinearMap =
          LinearMap.id := by
  sorry

end AlgebraicGeometry.Scheme
