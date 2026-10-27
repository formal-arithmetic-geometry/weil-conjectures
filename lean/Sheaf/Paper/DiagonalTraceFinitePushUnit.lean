/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTraceFiniteEvaluation

/-! # The coefficient-unit component of finite direct-image comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

/-- The normalized finite comparison sends the actual coefficient unit to the
geometric coefficient unit. Only the unit component is asserted, with no Chern
arrow, supported class, or arbitrary operation on Hom sets.

Source: diagonal tower trace proof (2), evaluation of the direct image;
geometric classes proof (3), the coefficient-pullback unit normalization.
(blueprint: lem-sfb-diagonal-trace-finite-push-unit).

Proof: the completed coefficient map and the coefficient projections commute
with inverse image, since both are induced by the unital finite quotient maps.
The coefficient_one and coefficient_projection equations identify this ordinary
square with the coefficientPullback normalization: each sends one to one.
Use the exact-cone projection identity to identify unitMap followed by projection
with the single of that ordinary quotient. The completed exact square and the
evaluation exact square transport that
ordinary square through their full common-unit equations. For the varying
comparison, its equation on K-injective complexes extends to the required
natural transformation by uniqueness of the right derived functor. The derived
adjunction on single objects identifies the derived coefficient adjunct with
the ordinary adjunct followed by the underived-to-derived direct-image unit.
Thus the ordinary square gives the same derived arrow on both routes. Cancel
the single-object comparisons and the varying isomorphism to obtain the
displayed equation.
The geometric coefficient arrow is the adjunction unit followed by pushforward
of coefficientPullback.derivedIso.hom, by homEquiv_apply. The ordinary unital
square therefore gives precisely this seed equation. The calculation uses the
positive quotient n+1, including n=0, and is valid on empty schemes. -/
theorem diagonalTrace_finitePush_unit (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let evS := ((evaluation ℕᵒᵖ (DiagonalMod l S)).obj (op n)).mapDerivedCategory
    p.finitePushUnit l ≫
        p.Rf.R.map (p.coefficientsX.unitMap l E p.LX ≫ (p.LX.projection n).app _) ≫
        (p.finitePushComparison l n).hom.app (SpTowerClasses.unit X
          (SpTowerClasses.Arings l E X)) =
      (p.coefficientsS.unitMap l E p.LS ≫ (p.LS.projection n).app _) ≫
        evS.map (p.restrictionS.F.mapDerivedCategory.map
          ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
            (p.model.coefficientPullback.derivedIso l E).hom)) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
