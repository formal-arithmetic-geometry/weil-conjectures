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


/-- Right Roos normalization before applying the quotient formula.
Source: Stacks 06YY, 07A4 and 0941; normalization of the scalar realization
and pullback model, before the explicit nested quotient identification.
(blueprint: stage3-pur-scalar-pullback-right-roos-normalized).

The proof compares the normalized scalar model with the pulled normalized model
on a coherent presentation, using the whole-system counit equation. The quotient
formula is not used in this normalization step.
-/
theorem scalarPullbackRightRoos_normalized (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L (W true))
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true) (ME.calculus true) ρ)
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (P : (integralOperationsGoodComplex.{u, u} l E (W false)).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E (W false))
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E (W false)) ℤ)
    (eC : (ME.calculus false).reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W false) n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W false) n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E (W false)
      (ME.calculus false).toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E (W false)
      (ME.calculus false) P.obj C eC κ)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L (W true)).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W false)).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι (W false)).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hF : IsSfDerivedComplete l E (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj)) :
    (SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj K.obj) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
          (pullbackReduction l E W ME f K.obj))) ≫
      scalarPullbackRoosCoordinate l E L ι f P C (ME.calculus false) ρ K.obj eP eC q =
    (scalarCompletionIso l E L ι (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj) hF).inv ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullback.{u, u} l E f).map eP.inv) ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullbackComparison.{u, u} l E f).hom.app P) ≫
      (integralOrdinaryScalar l E L ι (W true)).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor.{u, u} l E f).obj P.obj) ≫
      DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) := by
  sorry


end WeilConjectures.ScalarExtensionTower
