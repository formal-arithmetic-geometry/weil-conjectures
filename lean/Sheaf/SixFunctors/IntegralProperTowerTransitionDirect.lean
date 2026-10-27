/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge

/-! # Finite direct-image transition transport -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite direct-image evaluation and reduction maps transport the prescribed
successor map to `sfDirectImageTransition`.
Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 0D6E.
(blueprint: lem-sf-integral-proper-tower-transition-direct).
Proof: apply the transition equation in `Operations.DirectEvaluation` and then use
naturality of the restriction comparison on the reduction evaluation isomorphisms.
The resulting equality is transported through the exact scalar restriction. -/
theorem directImageEvaluationTransition (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {X Y : Scheme.{u}} (p : X ⟶ Y) (K : Integral l E X)
    (n : ℕ) :
    let N := (Operations.push l E o p).obj ((calculus l E X).reduction.obj K)
    (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          ((coefficientSequenceDerivedTransition l E Y n.le_succ).app N) ≫
        (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          ((normalizedDVRRes l E Y n.le_succ).map
            (((o.evaluation p).evaluation n).hom.app
              ((calculus l E X).reduction.obj K))) ≫
        (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          ((normalizedDVRRes l E Y n.le_succ).map
            ((proEtaleConstantDerivedDirectImage p
              (Padic.coefficientExtensionRing l E (n + 1))).map
              (((calculus l E X).reductionEvaluation n).hom.app K))) ≫
        (normalizedDVRResCompletedComp l E Y D hl n.le_succ).hom.app
          ((proEtaleConstantDerivedDirectImage p
            (Padic.coefficientExtensionRing l E (n + 1))).obj
            ((coefficientFiniteDerivedExtension l E X n).obj K)) =
      (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          (((o.evaluation p).evaluation (n + 1)).hom.app
            ((calculus l E X).reduction.obj K)) ≫
        (normalizedDVRResCompleted l E Y D hl (n + 1)).map
          ((proEtaleConstantDerivedDirectImage p
            (Padic.coefficientExtensionRing l E (n + 2))).map
            (((calculus l E X).reductionEvaluation (n + 1)).hom.app K)) ≫
        sfDirectImageTransition l E p K n := by
  sorry

end WeilConjectures.IntegralSystemRealization
