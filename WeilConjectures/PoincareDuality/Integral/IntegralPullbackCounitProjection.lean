/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackStrictFiniteComponent
import WeilConjectures.TraceFormula.Coherent.CoherentPrimitiveReductionPresentation
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Finite projection of the normalized coherent pullback counit

The counit projection is computed from a coherent strict quotient presentation,
the normalized Roos projection, and the finite inverse-image unit comparison.
Source: Stacks Tags 0941 and 099N(5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.integralDerivedPullback
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.coefficientFiniteDerivedRestriction
  WeilConjectures.integralComparisonDerivedSequencePullback
  WeilConjectures.coefficientConstantTowerLimit
  WeilConjectures.coefficientConstantTowerEvaluation
  WeilConjectures.coefficientSequenceLimit
  WeilConjectures.integralOperationsRoos WeilConjectures.integralOperationsRoosFunctor
  WeilConjectures.integralOperationsGoodComplex
  WeilConjectures.integralOperationsGoodLocalization
  WeilConjectures.integralOperationsPullbackOnGood
  WeilConjectures.integralOperationsPullbackComplexFunctor
  WeilConjectures.integralPullbackFiniteComplex
  WeilConjectures.integralOperationsPullbackTowerFunctor
  WeilConjectures.integralOperationsPullbackLevel WeilConjectures.integralOperationsRestrict
  WeilConjectures.scalarReductionDerivedRestriction
  HomologicalComplex.complexOfFunctorsToFunctorToComplex HomologicalComplex.asFunctor
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  WeilConjectures.unrestrictedIntegralReductionFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end WeilConjectures
