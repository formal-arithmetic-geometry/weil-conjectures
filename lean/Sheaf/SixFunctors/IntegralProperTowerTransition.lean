/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge

/-! # Proper realization and its defining projections -/

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

/-- Restricted direct-image evaluation carries the canonical quotient transition to
its prescribed finite-image transition.
Source: Stacks 0D6E and 0941; primitive realization Step 3
(blueprint: lem-sf-integral-proper-tower-transition).

Proof: compute the reduction of one flat-term K-flat representative as its single
quotient system. Its finite evaluation comparison is the quotient-complex model,
including the quotient maps. The transition equation in o.evaluation moves the
system quotient map past direct image. Its restrictedDirectCanonical field identifies
the resulting coefficient square with the canonical derived restriction square.
Both the restricted quotient map and sfDerivedReductionTransition are determined
by their ordinary pure-tensor quotient formula on K-flat representatives. The
restriction comparison is determined on K-injective models. These normalizations
therefore identify the transported successor map with sfDirectImageTransition.
Localization gives the equation on all integral inputs, including the zero input.
This is a transition equation, with no assertion of faithfulness of finite evaluation. -/
theorem integralProperTowerTransition (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {X Y : Scheme.{u}} (p : X ⟶ Y) (K : Integral l E X) :
    let M := (Operations.push l E o p).obj ((calculus l E X).reduction.obj K)
    let a := fun n : ℕ ↦
      (coefficientRestrictedEvaluationIso l E Y n).app M ≪≫
        (scalarReductionDerivedRestriction l E Y n).mapIso
          (((o.evaluation p).evaluation n).app ((calculus l E X).reduction.obj K) ≪≫
            (proEtaleConstantDerivedDirectImage p
              (Padic.coefficientExtensionRing l E (n + 1))).mapIso
                (((calculus l E X).reductionEvaluation n).app K))
    ∀ n : ℕ,
      (normalizedDVRTowerTransition l E Y D hl n.le_succ).app
          ((coefficientSequenceDerivedRestriction l E Y).obj M) ≫ (a n).hom =
        (a (n + 1)).hom ≫ sfDirectImageTransition l E p K n := by
  sorry

end WeilConjectures.IntegralSystemRealization
