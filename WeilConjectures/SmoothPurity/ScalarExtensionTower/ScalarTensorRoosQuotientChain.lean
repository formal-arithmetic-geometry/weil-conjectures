/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarTensorStrictQuotientTower

/-! # Roos transport of the strict scalar tensor quotient calculation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

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

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard integralOrdinaryScalar
  integralComparisonSequenceScalarModel coefficientSequenceRestriction
  completedIntegralCommRingSheafUnrestricted integralOperationsRoos integralOperationsRoosMap
  scalarRoosMap integralOrdinaryTensorSection unrestrictedIntegralTensorSection comparisons
attribute [local implicit_reducible] tensor integralOperationsTensorTowerFunctor
  integralOperationsRoosFunctor Functor.mapHomologicalComplex NatIso.mapHomologicalComplex

attribute [local irreducible] integralCompletedTensor scalarReduction tensorReduction
  scalarCompletion scalarTensorOrdinary

attribute [local irreducible] coefficientSequenceLimit Functor.mapDerivedCategory
attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar

end WeilConjectures.ScalarExtensionTower
