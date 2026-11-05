/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTowerTensorLimitStrictWitness
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarCompletionQuotientPresentation
import WeilConjectures.SmoothPurity.ScalarExtensionTower.IntegralScalarRoosCounitNormalization
import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTensorStrictQuotientTower
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTensorRoosQuotientChain
import all WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore

/-! # Good representative transport

The strict K-flat calculation is isolated from the later localization and
completed-limit assembly.
(blueprint: stage3-pur-scalar-tensor-limit-good-representatives)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.scalarReductionSourceDerived
  WeilConjectures.scalarReductionTargetDerived WeilConjectures.integralOperationsSiteSmall
attribute [local instance 3000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 50000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  WeilConjectures.integralOperationsAbSheafify WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible]
  integralCompletedTensor scalarReduction tensorReduction

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralOrdinaryScalar completedIntegralCommRingSheafUnrestricted
  comparisons Functor.leftAdjoint Functor.mapDerivedCategory SheafOfModules.monoidalCategory
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  integralOperationsRoos integralOperationsRoosMap scalarRoosMap scalarCompletion
  scalarTensorOrdinary coefficientTotalTensor integralOrdinaryTensorSection
  unrestrictedIntegralTensorSection integralTensorGenerator
  integralComparisonSequenceTensorSection integralComparisonRestrictedSection
  integralComparisonSequenceSection coefficientEvaluationSection
attribute [local implicit_reducible] tensor integralComparisonDerivedSequenceScalar
  integralOperationsTensorTowerFunctor integralOperationsTensorLevel
  integralScalarExtension integralScalarExtensionOfUniverses
  integralOperationsGoodLocalization integralOperationsRoosFunctor
  integralOperationsTensorComplexFunctor integralOperationsTensorOnGood

end WeilConjectures.ScalarExtensionTower
