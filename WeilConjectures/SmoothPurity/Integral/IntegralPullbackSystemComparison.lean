/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealization
import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import WeilConjectures.TraceFormula.Supporting.EffectiveQuotientModelDescent
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackCounitProjection
import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedQuotientPullbackRealizationNormalization

/-! # Integral pullback and coherent finite-system reduction

Source: Stacks Project, Tags 099N(5) and 0941; Bhatt--Scholze, Lemma 3.5.7
(blueprint: lem-pod-integral-pullback-system-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option allowUnsafeReducibility true in
attribute [local irreducible] integralSystemPullbackReductionIso
  integralDerivedPullback integralSystemReductionEvaluation
  finiteSystemDerivedPullbackEvaluation

set_option allowUnsafeReducibility true in
attribute [local reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientFiniteDerivedExtension constructibleIntegralPullback integralSystemReduction
  Functor.comp ObjectProperty.ι CategoryTheory.inducedFunctor

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end WeilConjectures
