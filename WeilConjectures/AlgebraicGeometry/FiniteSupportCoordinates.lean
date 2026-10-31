/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientTowerShriekInterfaces

/-! # Finite support coordinates without unused tower data

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
`sk-prop-sp-composition-comparisons.proof.md`, (3), first sentence
(blueprint: def-sp-coefficient-tower-shriek-interfaces).

This relocates the existing `fixedSupportCoordinatesFinite` helper unchanged from
`FiniteNormalizedCompositorFixedCoordinates`. Its defining word is exactly
`fixedSupportCoordinates` with the unused tower-base argument removed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

namespace SpTowerCalculus

/-- The published fixed support comparison with its unused tower-base argument removed.
The inner whisker is exactly `finiteSupportCoordinates`; the remaining word is exactly
`fixedSupportCoordinates`, including its realization units and counits. Thus this
interface requires only the section-normalized finite data, and no tower data.
Source: blueprint, composition comparisons proof (3), first sentence
(blueprint: def-sp-coefficient-tower-shriek-interfaces). -/
def fixedSupportCoordinatesFinite
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (z : FiniteCoordinates l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    reductionCompactSupport (SpTowerShriek.R l E n) c.i c.g ⋙
        (sfIntrinsicDerivedEquivalence Y (SpTowerShriek.R l E n)).inverse ≅
      (sfIntrinsicDerivedEquivalence X (SpTowerShriek.R l E n)).inverse ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n))) c :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorNatIso (z.direct c.g n))) _ ≪≫
    CategoryTheory.Iso.isoInverseComp ((Functor.associator _ _ _).symm ≪≫
      (sfIntrinsicCompactSupportComparison (SpTowerShriek.R l E n) c).compInverseIso)


end SpTowerCalculus

end AlgebraicGeometry.ProEtale
