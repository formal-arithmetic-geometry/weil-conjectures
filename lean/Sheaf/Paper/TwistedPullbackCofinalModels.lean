/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TwistedPullbackReductionData

/-! # Simultaneous cofinal reduction, pullback and tensor models

Source: blueprint integral-adjunction-bijection, Purity paragraph.
(blueprint: lem-sp-twisted-pullback-cofinal-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.SpTwistedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The cofinal restriction of strict uniformizer systems to ell-power systems,
with the canonical reduction counits and ordinary pullback and tensor comparisons.
Source: blueprint integral-adjunction-bijection, Purity paragraph; Stacks 0941,
06YY, 07A4; Bhatt--Scholze 3.5.7.
(blueprint: lem-sp-twisted-pullback-cofinal-models).

Proof: write ell = u*pi^e in the coefficient DVR. At index n restrict a strict
system to e(n+1)-1, using the identity-induced quotient-ring identifications.
Restriction acts on sections and maps literally, and is exact because kernels
and cokernels are computed componentwise. This constructs FX and FY, including
their scalar and restriction equations. For AX and AY use ordinary quotient
tensor on the sequence site and its resolving-class left-derived construction,
choosing the reduction functor to be the recorded universal reduction. Compare
ordinary cofinal quotient tensor to R.ordinary by the map sending 1 tensor x
to the recorded reduction generator. Tensor generation proves invertibility,
naturality and the quotient-unit formula. Uniqueness of left-derived functors
extends this comparison to cX and cY with the displayed counit normalization;
the ordinary adjunction unit gives their counit-transpose equation.
Direct image commutes with restriction on sections. Take its adjoint mate to
obtain G.inverseImage, retaining the mate equation. Finally restrict every total
tensor summand. The identity on its two local tensor factors constructs T.chain,
with inverse given by the same rebracketing. Acyclic tensor tests give T.kflat.
Localizing this chain comparison on K-flat pairs gives T.comparison and exactly
T.representative. The argument includes equal indices and all quotient maps,
and uses no evaluation to choose or lift a derived morphism. For the final
functorial transport, whisker the inverse of G.derived with integralSystemReduction,
then compose with the pullback of cY.derived on the constructible inclusion. Pair
this natural comparison with cX.derived at the reduced line. Whisker T.comparison
and this tensor comparison with the shift functor, after the exact restriction
shift comparison. The resulting natural isomorphism c has exactly the displayed
cofinalSourceComparison as its component, by the component formulas for functorial
whiskering, tensor and shift. This is a statement about native finite systems;
no completed-pullback comparison, constructibility, or reconstruction is assumed. -/
theorem twistedPullbackCofinalModels {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : SpTowerShriek.Base l E) (g : SpTowerShriek.Geometry l E b f)
    (DX : SpCoefficientTowersAbelian l E X) (RX : SpReductionTower l E X DX)
    (DY : SpCoefficientTowersAbelian l E Y) (RY : SpReductionTower l E Y DY) :
    ∃ (AX : IntegralStrictReductionModel l E X)
      (AY : IntegralStrictReductionModel l E Y)
      (FX : CofinalModel l E b X) (FY : CofinalModel l E b Y)
      (cX : CofinalReduction l E b X DX RX AX FX)
      (cY : CofinalReduction l E b Y DY RY AY FY)
      (G : CofinalGeometry l E b f g FX FY) (T : CofinalTensor l E b X FX),
      ∀ m s : ℤ,
        ∃ c : nativeFiniteSource l E f m s ⋙ FX.ordinary.mapDerivedCategory ≅
          finiteSource l E b f g DX RX DY RY m s,
          ∀ K : sfIntegralConstructibleCategory l E Y, c.app K =
            cofinalSourceComparison l E b f g DX RX DY RY AX AY FX FY cX cY G T m s K := by sorry

end WeilConjectures.SpTwistedPullback
