/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralScalarOperations.IntegralOperationsScalarExtension
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels

import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralScalarPullbackComparison
import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralScalarTensorComparison

import WeilConjectures.CategoryTheory.SmoothPurity.FunctorSquareTowerDescent
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackTowerRepresentatives
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackNormalizedTower
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorNormalizedTower
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarOrdinaryTensorChainTower
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarOrdinaryTensorTowerRepresentatives
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralScalarCompletion
import WeilConjectures.SmoothPurity.Normalized.NormalizedIntegralOrdinaryTensorChain
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarInternalHomComplete
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeTensor
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeHom
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # Normalized integral scalar comparisons

The finite-level maps, strict towers, and good-representative models are publicly
re-exported from IntegralOperationsScalarComparisonModels. This file retains the
ordinary derived comparisons, completed comparisons, and coherence statements.
(blueprint: lem-pur-integral-operations-scalar-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection integralCompletedScalarMap
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  coefficientTotalTensor
attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
attribute [local irreducible] constantSheaf limit
  integralDerivedPullback integralCompletedTensor integralScalarExtension

attribute [local irreducible] scalarIntegralClosed scalarIntegralModels

section ScalarClosedTensorDescent

end ScalarClosedTensorDescent

section ScalarHomBaseChange

end ScalarHomBaseChange

section ScalarHomCompleteness

end ScalarHomCompleteness

section ScalarTowerDescent

attribute [local irreducible] integralOrdinaryScalarComp integralOrdinaryDerivedScalarComp
attribute [local implicit_reducible] goodScalar
  integralOperationsPullbackOnGood integralOperationsTensorOnGood
  integralOperationsGoodLocalization

attribute [local irreducible] goodScalarComparison

attribute [local irreducible] scalarPullbackOrdinary scalarTensorOrdinary

end ScalarTowerDescent

end WeilConjectures
