/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralReconstructionComparisonData
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackReductionData

/-! # Interface comparisons for the integral adjunction

Source: latest blueprint, integral-adjunction-bijection, Normalization and Purity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpIntegralAdjunction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Reassociate the canonical pullback/twist/shift reduction into the ordered-line source.
Source: latest blueprint, integral-adjunction-bijection, Purity, and
lem-sp-twisted-pullback-reduction-tower
(blueprint: lem-sp-integral-adjunction-ordered-source).

Proof: the positive-power specialization of the integral signed-line reduction
identifies the reduced Tate line with the tensor power of the finite degree-one
Tate line. The normalized comparisons in w identify that line on entire strict
systems, including every quotient transition. Induct on d, starting with the
coefficient unitor for d=0. In the successor case use the tensor associator and
the shift/tensor comparison to move the next degree-one line shifted by 2 into
the ordered product. This gives tensor with the signed d-th line followed by
shift 2d isomorphic to tensor with SpTowerGamma.orderedLine w d. Whisker with
the recorded completed reduction and the same derived pullback o.geometry f.
Both sides use identical pullback coordinates; the only changed expression is
the tensor/shift word. The inclusion of reduce forgets its membership proof,
so its composite is the same ambient functor by proof irrelevance. Each map is
constructed before finite evaluation and respects every quotient transition.
No purity orientation, transpose or integral adjunction is involved. -/
theorem integralAdjunctionSourceComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (hX : ∀ x : X, Invertible (l : X.residueField x))
    (hY : ∀ y : Y, Invertible (l : Y.residueField y))
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) (w : SpChartAdmissibility.Twists l E X)
    (RX : SpReductionTower l E X (q.abelian X))
    (RY : SpReductionTower l E Y (q.abelian Y))
    (hY : ∀ K : sfIntegralConstructibleCategory l E Y,
      spConstructibleTorTowers l E Y (q.abelian Y)
        ((reduction l E Y (q.abelian Y) RY).obj K)) :
    Nonempty
      (SpTwistedPullback.finiteSource l E b f (o.geometry f)
          (q.abelian X) RX (q.abelian Y) RY (d : ℤ) (2 * (d : ℤ)) ≅
        reduce l E Y (q.abelian Y) RY hY ⋙
          SpTowerGamma.source l E b o q f w d) := by
  sorry

end AlgebraicGeometry.ProEtale.SpIntegralAdjunction
