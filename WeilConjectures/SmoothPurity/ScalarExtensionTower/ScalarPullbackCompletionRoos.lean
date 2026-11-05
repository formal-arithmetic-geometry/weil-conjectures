/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackRoosCoordinates
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarCompletionPresentationNormalization
import WeilConjectures.SmoothPurity.Supporting.FixedCalculusScalarModel
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackStrictTower
import WeilConjectures.SmoothPurity.ScalarExtensionTower.IntegralScalarRoosCounitNormalization
import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison
import all WeilConjectures.TraceFormula.Scalar.ScalarModelRoosZeroLiftCore
import WeilConjectures.SmoothPurity.Scalar.ScalarRoosFunctorNaturality
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Fixed cochain coordinates for the scalar/pullback calculation

Source: Stacks 06YY, 07A4 and 0941. The coordinates are constructed from the
ordinary scalar/pullback chain map and a coherent quotient presentation.
-/

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
