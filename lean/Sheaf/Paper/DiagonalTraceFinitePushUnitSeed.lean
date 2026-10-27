/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.DiagonalTraceFiniteEvaluation

/-! # The common-unit seed for finite direct-image comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

/-- The normalized completed coefficient unit agrees with the coefficient-unit
adjunct after the limit/direct-image comparison and the varying comparison.

Source: diagonal tower trace proof (2), ordinary coefficient-unit square;
geometric classes proof (3), coefficient-pullback unit normalization.
(blueprint: lem-sfb-diagonal-trace-finite-push-unit-seed).

Proof: evaluate the completed exact square on the degree-zero complex of the
completed coefficient unit. The completed unit map and its ordinary comparison
are the same unital map on sections. Evaluate the coefficient cone comparison
on the same complex and use its coefficient-one equation. The coefficient
pullback normalization identifies the resulting ordinary map with the
adjunction hom-equivalence of the coefficient-pullback derived isomorphism.
Finally apply the common normalization of the limit square and the naturality
of the varying comparison. All equalities are morphism equalities in the
corresponding derived categories; no finite projection or evaluation is used.
The argument also covers n=0 and empty schemes because only unital maps and
normalization equations are involved. -/
theorem diagonalTrace_finitePush_unit_seed
    (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    {f : X ⟶ S} (p : Presentation l (ULift.{u} (Padic l)) f) :
    (p.finitePushUnit l ≫
        p.Rf.R.map (p.coefficientsX.unitMap l (ULift.{u} (Padic l)) p.LX)) ≫
        p.limits.iso.hom.app (p.restrictionX.F.mapDerivedCategory.obj
          (SpTowerClasses.unit X (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X))) =
      p.coefficientsS.unitMap l (ULift.{u} (Padic l)) p.LS ≫
        p.LS.R.map (p.restrictionS.F.mapDerivedCategory.map
          ((SpTowerShriek.adjunction l (ULift.{u} (Padic l)) p.base p.model.geometry).homEquiv _ _
            (p.model.coefficientPullback.derivedIso l (ULift.{u} (Padic l))).hom)) ≫
        p.LS.R.map (p.varying.hom.app
          (SpTowerClasses.unit X (SpTowerClasses.Arings l (ULift.{u} (Padic l)) X))) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
