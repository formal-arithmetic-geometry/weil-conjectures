/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTraceFiniteEvaluation

/-! # The common-unit comparison before the varying isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

/-- The finite-push unit comparison after transporting backwards through the
varying derived isomorphism.

Source: diagonal tower trace proof (2), ordinary coefficient-unit square;
geometric classes proof (3), coefficient-pullback unit normalization.
(blueprint: lem-sfb-diagonal-trace-finite-push-unit-common).

Proof: evaluate the completed exact square on the degree-zero complex of the
completed coefficient unit.  Expand the coefficient cone comparison and use
the coefficient-one and coefficient-projection equations.  The
coefficient-pullback normalization identifies the resulting map with the
adjunction hom-equivalence, and the limit-square common-unit equation gives
the displayed equality after composing with the inverse varying comparison.
The statement is the pre-varying step; composing with the varying isomorphism
is the final categorical step in the seed theorem. -/
theorem diagonalTrace_finitePush_unit_common
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) :
    ((p.finitePushUnit l ≫
        p.Rf.R.map (p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX)) ≫
        p.limits.iso.hom.app (p.restrictionX.F.mapDerivedCategory.obj
          (SpTowerClasses.unit X (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X)))) ≫
        p.LS.R.map (p.varying.inv.app
          (SpTowerClasses.unit X
            (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X))) =
      p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
        p.LS.R.map (p.restrictionS.F.mapDerivedCategory.map
          ((SpTowerShriek.adjunction l (ULift.{u} (Padic l)) p.base p.model.geometry).homEquiv _ _
            (p.model.coefficientPullback.derivedIso l (ULift.{u} (Padic l))).hom)) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
