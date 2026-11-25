/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Tensor.PodReindexingTensorCoefficientTransitionDescentData

/-! # Scalar normalization for scalar/reindexing tensor descent

The scalar tensor chain on a pair of good constructible representatives is identified with the
scalar tensor normalization `scalarTensorOrdinary` and the derived factor maps of scalar
extension.

## Implementation details

This is the defining unique normalization of `scalarTensorOrdinary` on the chosen good pair.

## References

* Stacks Project, Tags 03EL, 05RU, 06YY, 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] podTensorReindexAdditive podTensorScalarZero podTensorMixedLeftZero
    podTensorMixedRightZero
  podTensorReindexLimits podTensorReindexColimits
attribute [local irreducible] integralCompletedTensor integralOrdinaryScalar
  integralOperationsTensorTowerFunctor scalarTensorChain scalarTensorOrdinary
  integralOperationsRoos completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted coefficientTotalTensor SheafOfModules.monoidalCategory
attribute [local implicit_reducible] podOrdinaryReindex podGoodReindex
  integralOperationsGoodLocalization integralOperationsTensorComplexFunctor
  integralOperationsRoosFunctor integralOperationsTensorOnGood
  scalarReductionSourceDerived integralTowerHasDerivedCategory
  integralOperationsCommHasDerivedCategory
  podTensorScalarGoodFunctor podTensorScalarGoodComparison podTensorReindexGoodComparison
  podTensorGoodConstructibleLocalization
  podTensorGoodConstructible podTensorMixedTensorIso podTensorGoodCoefficientTransition
  podTensorTensorReindexDerivedChain
  podTensorTensorScalarDerivedChain podTensorTensorMixedDerivedChain

/-- Scalar normalization on representatives: for good constructible `P, Q`, the completed tensor
comparison followed by the scalar derived chain equals `scalarTensorOrdinary`, the tensor of the
scalar-extension factor maps, and the completed tensor comparison at the scalar-extended pair. -/
theorem podTensorScalarRepresentativeNormalization
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (_hD : PodCompletionReindex.Laws l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (_hT : PodCompletedTensorReindex.Laws l E g D T)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (D' : PodCompletionReindex l L g) (_hD' : PodCompletionReindex.Laws l L g D')
    (T' : PodCompletedTensorReindex l L g D')
    (_hT' : PodCompletedTensorReindex.Laws l L g D' T')
    (S : PodReindexCoefficientTransition l E L ι g D D')
    (_hcore : PodReindexCoefficientTransition.Core l E g L ι D D' S)
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    (integralOrdinaryDerivedScalar l E L ι X).map
        ((integralCompletedTensorComparison l E X).hom.app (P, Q)) ≫
      podTensorTensorScalarDerivedChain l E L ι X P Q =
    (scalarTensorOrdinary l E L ι X).hom.app
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      (integralCompletedTensor l L X).map
        (Prod.mkHom ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app P.obj)
          ((integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
      (integralCompletedTensorComparison l L X).hom.app
        ((podTensorScalarGoodFunctor l E L ι X).obj P,
          (podTensorScalarGoodFunctor l E L ι X).obj Q) := by
  have hn : scalarTensorOrdinaryNormalization l E L ι X
      (scalarTensorOrdinary l E L ι X) := by
    unfold scalarTensorOrdinary
    exact (scalarTensorOrdinary_existsUnique l E L ι X).exists.choose_spec
  exact hn P Q

end WeilConjectures
