/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerGenericTransitions


/-! # Strict transitions in intrinsic coefficient coordinates

Source: Zheng, Construction 4.1; Stacks 07A6; the first step of the
coefficient-tower transition compatibility argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The normalized generic compact-support evaluation preserves the actual strict
transition before transport to original tower coordinates.
Source: Zheng 4.10; Stacks 0D6D and 0D6E; blueprint Levels paragraph.
Proof: for the proper factor apply Geometry.transitionFormula and take its scalar
adjunction transpose. The coefficient mate is normalized by the geometric counit,
so its restriction comparison is the prescribed inverse direct-image restriction
comparison. For the open factor, apply its ordinary adjunction to the transition
square. Its unit_evaluation and counit_evaluation reduce this to the pullback
transition square: both maps place the horizontal transition into the same open
structural summand. Localize the resulting ordinary open square termwise. Paste
with the proper square, cancel the middle evaluation comparisons, and unfold
Fcomparison. The pasted restriction comparison is intrinsicCompactSupportRestriction.
The argument applies to all ambient derived systems and uses no finite-Tor premise.
(blueprint: lem-sp-tower-generic-compact-support-transition). -/
theorem generic_compactSupport_intrinsicTransition
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : SpTowerShriek.D l E X) {m n : ℕ} (v : m ≤ n) :
    (genericIntrinsicTransitions l E Y v).app ((SpTowerShriek.F l E b o c).obj K) ≫
      (scalarRestriction (quotient l E v) Y).map
        ((SpTowerShriek.Fcomparison l E b o c m).hom.app K) =
    (SpTowerShriek.Fcomparison l E b o c n).hom.app K ≫
      (reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g).map
        ((genericIntrinsicTransitions l E X v).app K) ≫
      (intrinsicCompactSupportRestriction (quotient l E v) c.i c.g).hom.app
        ((SpTowerShriek.Ev l E X m).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerCalculus
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
