/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.TraceFormula.Scalar.ScalarModelRoosCounitNormalization

/-! # The normalized Roos counit in the ordinary integral scalar model -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] HasDerivedCategory.standard
  integralComparisonSequenceScalarModel coefficientSequenceRestriction coefficientSequenceLimit
  integralDerivedPullback integralOrdinaryScalar integralComparisonSequenceScalarPullback
  completedIntegralCommRingSheafUnrestricted
  integralOperationsRoos integralOperationsRoosMap scalarRoosMap

attribute [local implicit_reducible] integralScalarExtension integralScalarExtensionOfUniverses
  integralComparisonDerivedSequenceScalar completedOrdinaryScalarComplex
  integralScalarComplexFunctor integralOperationsGoodLocalization
  integralOperationsRoosFunctor integralOperationsPullbackComplexFunctor
  NatIso.mapHomologicalComplex Functor.mapHomologicalComplex
  integralOperationsPullbackOnGood integralComparisonSequencePullback
  integralComparisonDerivedSequencePullback HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex

end WeilConjectures.ScalarExtensionTower
