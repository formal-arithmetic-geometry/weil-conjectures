/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ShriekNormalizedTransitionData

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
/-- Open extension carries the actual reduction to its normalized open scalar word.
Source: blueprint integral-adjunction direct-image paragraph (1), step 2;
Stacks 03DI and 06YY; Zheng 4.1.
Proof: use the ordinary open adjunction and its evaluated units/counits to identify
extension of the strict transition with the coefficient-restriction square. Derive
the square termwise, since both open extension and restriction are exact. Transpose
under scalar adjunction. The normalized open units and uniqueness of composite left
adjoints identify this comparison with reductionOpenScalarIso. The scalar coordinate
maps preserve the units, and substitution gives the equality. Zero and empty opens,
equal indices, and noninvertible input transitions obey the same calculation.
(blueprint: lem-sp-normalized-open-transition). -/
theorem normalized_open_transition (b : SpTowerShriek.Base l E)
    {U T : Scheme.{u}} {j : U ⟶ T} [IsOpenImmersion j]
    {g : SpTowerShriek.Geometry l E b j} (a : SpTowerShriek.Open l E b j g)
    {m n : ℕ} (h : m ≤ n) (M : SpTowerShriek.D l E U) :
    rho l E b T h ((SpTowerShriek.openD l E b a).obj M) ≫
        (SpTowerShriek.openEvaluation l E b a m).hom.app M =
      (scalarExtensionFunctor (quotientMap l E h) T).map
          ((SpTowerShriek.openEvaluation l E b a n).hom.app M) ≫
        (reductionOpenScalarIso (quotientMap l E h) j).hom.app
          ((SpTowerShriek.Ev l E U n).obj M) ≫
        (sfIntrinsicDerivedOpen (SpTowerShriek.R l E m) j).map (rho l E b U h M) := by
  sorry

end AlgebraicGeometry.ProEtale.SpShriekTransition
