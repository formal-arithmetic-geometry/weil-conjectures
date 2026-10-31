/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionData

/-! # The normalized transition of one geometric operation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpShriekTransition
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local irreducible] scalarCoordinates quotientMap
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Direct-image transition in the specified constant-ring coordinates.
Source: Zheng 4.10 and blueprint integral-adjunction direct-image paragraph (1).
Proof: transport Geometry.transitionFormula along its coefficient, target-calculus,
level-adjunction and evaluation identifications. Left-adjoint uniqueness makes the
scalar coordinate maps preserve units. Use ordinaryPullTransition and the specified
ordinaryUnitTransition on finite geometric units to identify the restriction square
with the canonical constant-ring square. Transpose that square: the coefficient mate
is the transpose of the scalar-extended counit, namely directImageScalarComparison.
Substitute into the generic formula and use scalar-coordinate naturality.
This works in ambient derived categories without flatness or Tor hypotheses.
(blueprint: lem-sp-normalized-proper-transition). -/
theorem normalized_proper_transition (b : SpTowerShriek.Base l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E X) :
    rho l E b Y h ((SpTowerShriek.push l E b g).obj M) ≫
        (g.pushEvaluation m).hom.app M =
      (scalarExtensionFunctor (quotientMap l E h) Y).map
          ((g.pushEvaluation n).hom.app M) ≫
        (directImageScalarComparison (quotientMap l E h) f).app
          ((SpTowerShriek.Ev l E X n).obj M) ≫
        (directImageConstantPush (SpTowerShriek.R l E m) f).map (rho l E b X h M) := by
  sorry

end AlgebraicGeometry.ProEtale.SpShriekTransition
