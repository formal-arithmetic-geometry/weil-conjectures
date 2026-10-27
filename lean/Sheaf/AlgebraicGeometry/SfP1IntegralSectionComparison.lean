/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X6
-/
module

public import Sheaf.AlgebraicGeometry.SfP1IntegralTransportData

/-! # Transport of the diagonal section unit

This equation is independent of any Tate twist, Ext representative or trace.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- Proper exchange and forget-supports carry the compact-support diagonal section
unit to the ordinary section unit, under an isomorphism over the base.

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the canonical identification
M = Rp2_* Delta_* M and the paragraph on substituting the exchange counits;
lem-amb-p1-diagonal-integrals.proof.md, the diagonal is a section for either projection.
(blueprint: lem-sf-p1-integral-section-comparison).

Proof: For either projection p, the square induced by i and i times i is
Cartesian, as is the diagonal square. Paste these squares. Their vertical
composite is the square for p Delta = id, so the composite-adjunction unit
formula makes exchange applied to the diagonal unit equal to the unit of the
identity adjunction. The ordinary projectiveLineDiagonalAlpha is exactly the
composite of the constant-object units for p and Delta. The compact-support
section map is the inverse identity/composition comparison. Forget-supports
identifies these composition comparisons: use the identity compactification for
the proper maps and independence from compactification, then the ordinary
composition mate formula. Thus both composites are the same section unit.
Finally the constant inverse-image comparison and the constant-sheaf/derived
monoidal-unit comparison identify the source; their inverses occur in
diagonalLift and constantComparison in precisely the displayed directions.
This calculation uses no coefficient line, Ext class, trace, nonempty-base
hypothesis, or nonzero-ring hypothesis. -/
theorem sectionComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (a : Bool) :
    diagonalUnit A f a ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).map
          (diagonalLift A f i hi) ≫
        (projectionComparison A f i hi a).hom.app
          ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (ordinaryFiniteUnit A (ProjectiveLine S))) =
      (constantComparison A i).inv ≫
        (ordinaryFinitePullback A i.hom).map (projectiveLineDiagonalAlpha A S a) := by sorry

end AlgebraicGeometry.Etale.SfP1Transport
