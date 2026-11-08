/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisonModels
public import Submission.WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition

import all Submission.WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all Submission.WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import Submission.WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import Submission.WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarPullbackLevelConstruction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Coherent scalar squares on pullback representatives

The exact scalar factors and the normalized chain maps form coherent squares before
localization. Source: coefficient-comparison coherence, Stacks 07A4 and 08J9.
(blueprint: lem-pur-integral-scalar-pullback-tower-representatives).
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

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u+1} W.ProEt := essentiallySmallSelf.{0, u, u+1} _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
      AddCommGrpCat.{u+1} := integralCoefficientAbLocallyBijective.{u, u} W

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] integralOperationsPullbackComplexFunctor
  integralOperationsTensorComplexFunctor integralOperationsPullbackTowerFunctor
  integralOperationsTensorTowerFunctor scalarPullbackChain scalarTensorChain
attribute [local irreducible] constantSheaf limit
  integralDerivedPullback integralCompletedTensor integralScalarExtension

section ScalarTowerDescent

attribute [local irreducible] integralOrdinaryScalarComp

attribute [local implicit_reducible] integralOperationsPullbackOnGood
  integralOperationsTensorOnGood integralOperationsGoodLocalization

private def goodScalar (W : AlgebraicGeometry.Scheme.{u}) :=
  (integralOperationsGoodComplex l L W).lift
    ((integralOperationsGoodComplex l E W).ι ⋙
      (integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ))
    (fun P ↦ scalarGood l E L ι W P)

attribute [local implicit_reducible] goodScalar

private def goodScalarComparison (W : AlgebraicGeometry.Scheme.{u}) :
    integralOperationsGoodLocalization l E W ⋙ integralOrdinaryDerivedScalar l E L ι W ≅
      goodScalar l E L ι W ⋙ integralOperationsGoodLocalization l L W :=
  Functor.isoWhiskerLeft (integralOperationsGoodComplex l E W).ι
    (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors

attribute [local implicit_reducible] goodScalarComparison

attribute [local irreducible] integralOrdinaryDerivedScalarComp

private def pullbackRep {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    integralOperationsGoodLocalization l E Y ⋙ integralDerivedPullback l E f ≅
      (integralOperationsGoodComplex l E Y).ι ⋙
        integralOperationsPullbackComplexFunctor l E f ⋙ DerivedCategory.Q :=
  integralDerivedPullbackComparison l E f

attribute [local implicit_reducible] pullbackRep

end ScalarTowerDescent
end WeilConjectures
