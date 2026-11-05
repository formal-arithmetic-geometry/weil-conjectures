/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarPullbackQuotientFormula
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarOrdinaryPresentationCoordinates
import all WeilConjectures.SmoothPurity.IntegralCoherence.IntegralGoodQuotientPresentation
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitModels
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarDataExistence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import all WeilConjectures.SixFunctors.SequenceScalarConstruction.SystemScalarPackageExists
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.OrdinaryScalarTowerProof
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitOrdinaryAdjunction
import WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientPullbackTowerComparison

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

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension integralOrdinaryScalar
  completedIntegralCommRingProjectionUnrestricted constantSheaf HasDerivedCategory.standard
  unrestrictedIntegralTensorSection integralOrdinaryTensorSection integralScalarTensorSection

attribute [local implicit_reducible] integralCoefficientCommRingSheaf integralCoefficientSheaf
  unrestrictedIntegralReductionFunctor Functor.mapHomologicalComplex
  SemilinearSections.systemRing coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf

end WeilConjectures.ScalarExtensionTower
