/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ScalarPullbackRoosCoordinates

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

/-- Compute the route using scalar normalization at Y and pullback normalization
with coefficients L. There is no scalar model at X or pullback model for E here.
Source: Stacks 07A4, 0941; the left route in realization step 8 of
lem-pur-scalar-extension-tower-coherence.
(blueprint: stage3-pur-scalar-pullback-left-roos).

Proof: precompose by scalarCompletionIso at the pulled E input. Its inverse in
scalarPullbackCompleted cancels. Naturality of the L-pullback realization moves
the remaining scalarCompletion at Y into the reduction diagram. Use the scalar
normalization of SY on the coherent presentation C, and the normalization of the
L-pullback on the ordinary scalar extension of P. The normalized completion chain
has the tensor-unit augmentation and zero shifted coordinate. The quotient
formula for q identifies its augmentation with the canonical scalarPullbackTower
map, level by level and with every transition. Applying the Roos functor gives
scalarPullbackChain on both coordinates. The normalization of
scalarPullbackOrdinary identifies its localization with the middle of the
conjugated completed comparison. Move eP through the natural transformations,
then cancel the source completion isomorphism. This proves the stated one-sided
coordinate formula. No realization with E after pullback is used. -/
theorem scalarPullbackLeftRoos (W : Bool → Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E (W false))
    (ML : CompletedOperations.Models.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι (W false) SE (ML.roos false))
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (P : (integralOperationsGoodComplex.{u, u} l E (W false)).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E (W false))
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E (W false)) ℤ)
    (eC : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W false) n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W false) n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E (W false)
      SE.toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E (W false) SE P.obj C eC κ)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L (W true)).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W false)).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι (W false)).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hq : ScalarPullbackQuotientFormula l E L ι f P C κ q)
    (hF : IsSfDerivedComplete l E (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj)) :
    (((scalarPullbackCompleted l E L ι f K.obj K.property.1 hF).hom ≫
        (ML.pullback f).realization.hom.app
          ((integralScalarExtension.{u} l E L ι (W false)).obj K.obj) ≫
        (coefficientSequenceLimit.{u, u} l L (W true)).map
          ((integralComparisonDerivedSequencePullback.{u, u} l L f).map
            (scalarReduction l E L ι (W false) SE (ML.calculus false)
              (ML.roos false) SY K.obj))) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonSystemScalarPullback.{u, u} l E L ι f).inv.app
          (SE.reduction.obj K.obj))) ≫
      scalarPullbackRoosCoordinate l E L ι f P C SE (ML.roos true) K.obj eP eC q =
    scalarPullbackRoosChain l E L ι f P K.obj eP hF := by
  sorry

end WeilConjectures.ScalarExtensionTower
