/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackQuotientFormula
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelReduction
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarFiniteReductionMaps
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackSuccessor
import all WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # The strict quotient square for scalar change and pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

attribute [local irreducible] HasDerivedCategory.standard
  integralOrdinaryScalar integralOrdinaryTensorSection integralComparisonSequenceScalarModel
  coefficientSequenceRestriction integralComparisonSequenceScalarPullback
  completedIntegralCommRingSheafUnrestricted unrestrictedIntegralTensorSection

attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict Functor.mapHomologicalComplex
  integralCoefficientCommRingSheaf integralCoefficientSheaf
  integralOperationsLevelPullback unrestrictedIntegralReductionFunctor
  integralComparisonSequencePullback integralComparisonSequenceDirectImage

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

end WeilConjectures.ScalarExtensionTower
