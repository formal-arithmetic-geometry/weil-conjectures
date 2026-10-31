/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalPurityScalarModels
public import WeilConjectures.AlgebraicGeometry.PbcDescentFunctors

/-! # Exact descent of twisted PBC pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
    [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f) (d : ℕ)
    [QuasiCompact f] [IsNoetherian X] [IsNoetherian Y]
    [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
    [iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
    [iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

attribute [local instance high] Algebra.toModule ScalarLocalization.category
attribute [local irreducible] ScalarLocalization.composition ScalarLocalization.transportHom
  pbcRationalScalarHom pbcPurityTwisted pbcPurityCompact
  pbcPurityTwistedAmbient pbcPurityCompactAmbient
  pbcPurityTateModel pbcPurityDerivedScalarModel purCoefficientModel
  integralSheafTwist completedDerivedScalarExtension pbcTateAmbient purScalarModel
  integralTwistOrdinaryBeta pbcPurityTateScalarModel pbcPurityTateScalarComponent
  pbcActualCompletedPull

attribute [local irreducible] pbcPurityStageTwisted pbcPurityStageCompact
  pbcPurityStageA pbcPurityStageC

/-- Exactness of the descended twisted-pullback functor, once its already specified
coefficient comparisons satisfy associator coherence.

Source: prop-pur-rational-purity-transitivity-summands, Steps 2--5; current
blueprint sk-prop-sp-rational and the coefficient-change clause of
sk-thm-purity-transport.
(blueprint: lem-pur-pbc-twisted-exact-descent).

Proof: completed pullback, tensor with the invertible Tate line, and the even
shift [2d] preserve the complete constructible lattice category and its
triangles. Use their standard derived shift comparisons. The specified scalar
comparison is the composite of pullback/scalar interchange, the Tate tensor
comparison, and shift/scalar interchange; each commutes with these shift
comparisons (the shift is even, so the shift interchange introduces no sign).
Restriction to the full lattice category preserves all these equations.
Apply scalar-localization exact transport to obtain additive triangulated
finite-stage functors and shift-compatible beta maps. The supplied associator
coherence makes these data a CoherentExactMorphism of the actual pbcScalarSystem
families. Apply pbcDescentFunctors and retain its ExactDescent clause. No new
coherence is assumed beyond the given equation, and its proof is irrelevant;
the pair-category functor is the published one. Identity extensions, zero
objects, d = 0, and empty schemes use the same comparisons. -/
theorem pbcPurityTwisted_exactDescent
    (hcoh : ∀ {E F L : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) (k : F ≤ L)
      (K : pbcStageCategory l Ω Y E),
      ((pbcScalarSystem l Ω X dX.out iX.out).T k).map
          ((pbcPurityStageA l Ω f c d h).hom.app K) ≫
        (pbcPurityStageA l Ω f c d k).hom.app
          (((pbcScalarSystem l Ω Y dY.out iY.out).T h).obj K) ≫
        (pbcPurityStageTwisted l Ω f c d L).map
          (((pbcScalarSystem l Ω Y dY.out iY.out).assoc h k).hom.app K) =
      ((pbcScalarSystem l Ω X dX.out iX.out).assoc h k).hom.app
          ((pbcPurityStageTwisted l Ω f c d E).obj K) ≫
        (pbcPurityStageA l Ω f c d (h.trans k)).hom.app K) :
    StageSystem.Morphism.ExactDescent
      ({ Φ := pbcPurityStageTwisted l Ω f c d
         β := pbcPurityStageA l Ω f c d
         coh := hcoh } : StageSystem.Morphism
        (pbcScalarSystem l Ω Y dY.out iY.out) (pbcScalarSystem l Ω X dX.out iX.out)) := by
  sorry

end AlgebraicGeometry.Scheme
