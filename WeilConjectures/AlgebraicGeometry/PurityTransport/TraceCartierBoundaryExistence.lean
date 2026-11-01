/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasicDefs
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceCartierBoundaryData.TraceCartierBoundaryPrimitives

/-! # Integral boundary data for native Cartier families

This is the construction part of the native Cartier existence argument.
(blueprint: new-det-sp-trace-cartier-boundary-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport.TraceCartierBoundaryData
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- A family is boundary-realized when every member is induced by one full
integral pro-etale Kummer boundary.  The intermediate Ext representative is
retained to make the source comparison explicit.
Source: the relative frame-torsor and integral Kummer construction in
`sk-def-sp-trace-properties.proof.md`, (2)
(blueprint: new-det-sp-trace-boundary-realization). -/
def TraceCartierBoundary (C : TraceCartierFamily.{u} ell) : Prop :=
  ∀ (c : Coefficient ell) {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hT : IsUnit (ell : Γ(T, ⊤))),
    ∃ (K : IntegralKummer ell T) (a : Class ell c i),
      a.hom = closedSingleMap ell c i ≫ C c i hI hT ∧
        Normalized ell i hI K c a


/-- The full integral Kummer boundary can be assembled simultaneously for all
native coefficients and Cartier immersions.  The construction uses the inverse
limit of the positive root tower, the relative pole extension, and scalar
extension from the integral coefficient ring.  The source unit is fixed by the
closed-support adjunction, so the resulting family is determined before any
finite evaluation.  Empty supports and the zero coefficient ring are included
because the same constructions are defined there.
Source: `sk-def-sp-trace-properties.proof.md`, (2), first paragraph
 (blueprint: new-det-sp-trace-cartier-boundary-existence). -/
theorem traceCartier_boundary_exists :
    ∃ C : TraceCartierFamily.{u} ell, TraceCartierBoundary ell C := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
