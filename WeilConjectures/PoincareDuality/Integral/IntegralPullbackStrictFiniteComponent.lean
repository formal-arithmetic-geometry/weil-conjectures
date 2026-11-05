/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The finite component of a strict normalized pullback comparison

Source: Stacks Tags 03D3, 099N(5), and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Replaying sectionwise transport proofs for tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.mapDerivedCategoryCompIso
  CategoryTheory.Functor.mapDerivedCategoryNatIso
attribute [local implicit_reducible] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
attribute [local implicit_reducible] WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.coefficientFiniteDerivedRestriction
  WeilConjectures.coefficientConstantTowerEvaluation
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  CategoryTheory.NatIso.mapHomologicalComplex CategoryTheory.NatTrans.mapHomologicalComplex
  HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
attribute [local irreducible] CategoryTheory.constantSheaf CategoryTheory.presheafToSheaf
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Exact evaluation after scalar restriction, computed on a complex of strict systems.
Source: Stacks 0941 (blueprint: lem-pod-integral-pullback-strict-finite-component). -/
@[irreducible] def integralComparisonRestrictedEvaluationFactors (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (coefficientFiniteDerivedRestriction l E W n).obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj
        ((((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (.up ℤ)).obj C).asFunctor.obj (op n)) :=
  ((coefficientRestrictedEvaluationIso l E W n).app (DerivedCategory.Q.obj C)).symm ≪≫
    (coefficientConstantTowerEvaluation l E W n).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app C) ≪≫
    (coefficientConstantTowerEvaluationFactors l E W n).app
      (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)

section Generators

attribute [local instance 30000] zeroOfFiniteLimits

attribute [local instance 50] additiveOfFiniteLimits

attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits
attribute [local irreducible] coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

attribute [local irreducible] restrictionEvaluation

attribute [local instance] finitePullback_limits finitePullback_colimits
  nativeFinitePullback_limits nativeFinitePullback_colimits
  mixedFinitePullback_limits mixedFinitePullback_colimits

attribute [local irreducible] finiteEvaluation

attribute [local irreducible] strictLevel

end Generators

section FiniteEvaluationFactors
attribute [local instance 30000] zeroOfFiniteLimits
attribute [local instance 50] additiveOfFiniteLimits
attribute [local instance]
  finitePullback_limits finitePullback_colimits nativeFinitePullback_limits
  nativeFinitePullback_colimits mixedFinitePullback_limits mixedFinitePullback_colimits
attribute [local irreducible] restrictionEvaluation finiteEvaluation strictLevel
attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits
attribute [local irreducible] coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

end FiniteEvaluationFactors

section Proof
attribute [local instance 30000] zeroOfFiniteLimits
attribute [local instance 50] additiveOfFiniteLimits
attribute [local instance]
  finitePullback_limits finitePullback_colimits nativeFinitePullback_limits
  nativeFinitePullback_colimits mixedFinitePullback_limits mixedFinitePullback_colimits
attribute [local irreducible] restrictionEvaluation finiteEvaluation strictLevel
attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits
attribute [local irreducible] coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

end Proof

attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local irreducible] strictLevel restrictionEvaluation finiteEvaluation
  coefficientSequenceRestriction completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

end WeilConjectures
