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


/-- The scalar completion augmentation respects the pulled coherent quotient tower.
Source: Stacks 06YY, 07A4 and 0941; the quotient calculation in step 1 of
stage3-pur-scalar-pullback-right-roos-normalized.
(blueprint: lem-pur-scalar-pullback-completion-roos).

Proof: transpose the reduction of eR followed by pullbackReduction through the
reduction/limit adjunction. Its counit cancels the reduction of the E-pullback
realization. Pullback normalization identifies the remaining transpose with the
strict pullback tensor-unit tower map attached to (C,eC,kappa). Coherence of
(D,eD,kappaD) identifies its source with the strict quotient tower of R.
At each level, associate the scalar tensors and apply the inverse-image unit.
The scalar/pullback association sends 1 tensor gamma(x) to gamma(1 tensor x).
The formulas hqD and hq identify the two resulting strict tower maps: balancing
and the inverse-image adjunction reduce equality to these nested unit sections.
Every map used is a map of quotient systems, so these equalities preserve all
horizontal transitions before localization. Apply the Roos construction to this
strict equality. The unshifted coordinates are the finite quotient projections
of the scalar completion augmentation; both shifted coordinates are zero.
The scalar/Roos product map followed by scalarPullbackTower is scalarPullbackChain.
Naturality of the K-injective-normalized Roos bridges transports this calculation
to derived limits. The comparison eR and then eP give the ordinary derived maps
on the right. The scalar cochain counit is inverted only through the supplied
isomorphism epsilonD. No scalar realization model, scalar completion inverse,
derived completeness, constructibility of the pulled object, or faithfulness of
finite derived evaluations is used. Zero complexes, identity maps, exponent one,
empty sites and ramified coefficient embeddings use the same balanced tensors. -/
theorem scalarPullbackCompletionRoos (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L (W true))
    (f : W true ⟶ W false)
    (P : (integralOperationsGoodComplex.{u, u} l E (W false)).FullSubcategory)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E (W false)))
    (eP : DerivedCategory.Q.obj P.obj ≅ K)
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
    (hq : ScalarPullbackQuotientFormula l E L ι f P C κ q)
    (R : (integralOperationsGoodComplex.{u, u} l E (W true)).FullSubcategory)
    (eR : DerivedCategory.Q.obj R.obj ≅
      (integralDerivedPullback.{u, u} l E f).obj K)
    (D : CochainComplex (coefficientSequenceModules.{u, u} l E (W true)) ℤ)
    (eD : (ME.calculus true).reduction.obj (DerivedCategory.Q.obj R.obj) ≅
      DerivedCategory.Q.obj D)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W true) n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W true) n).obj R.obj)
    (hpD : CoefficientReductionPresentation.{u, u} l E (W true)
      (ME.calculus true).toCoefficientDerivedSystemReduction R.obj R.property.1 D eD κD)
    (hcD : IsIntegralComparisonPresentationCoherent.{u, u} l E (W true)
      (ME.calculus true) R.obj D eD κD)
    (εD : (integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).obj
        (DerivedCategory.Q.obj D) ≅
      DerivedCategory.Q.obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W true)).E.mapHomologicalComplex
          (.up ℤ)).obj D))
    (hεD : εD.hom = (integralComparisonSequenceScalarModel.{u, u} l E L ι (W true)).ε.app D)
    (qD : (((coefficientSequenceRestriction.{u, u} l L (W true)).mapHomologicalComplex
        (.up ℤ)).obj
      (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W true)).E.mapHomologicalComplex
        (.up ℤ)).obj D)).asFunctor ≅
      (integralScalarTowerFunctor.{u, u} l E L ι (W true)).obj R.obj)
    (hqD : ∀ (n : ℕ) (i : ℤ) (U : (W true).ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L (W true)).obj.obj (op (n, U.unop)))
        (x : (R.obj.X i).val.obj U),
        ((qD.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l L (W true)
            ((integralComparisonSequenceScalarModel l E L ι (W true)).E.obj (D.X i)) n U
            (integralComparisonSequenceTensorSection l E L ι (W true) (D.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E (W true) (D.X i) n U
                (((κD n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E (W true) n (R.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E L ι (W true) n (R.obj.X i) U s x) :
    let T := coefficientSequenceLimit.{u, u} l L (W true)
    let A := integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)
    let SD :=
      ((integralComparisonSequenceScalarModel.{u, u} l E L ι (W true)).E.mapHomologicalComplex
        (.up ℤ)).obj D
    let rD := T.mapIso (A.mapIso eD ≪≫ εD) ≪≫
      integralComparisonRoosBridge.{u, u} l L (W true) ρ SD ≪≫
      DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso qD)
    (integralOrdinaryScalar l E L ι (W true)).mapDerivedCategoryFactors.hom.app R.obj ≫
      DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι (W true)).app R.obj) ≫
      rD.inv ≫
      T.map (A.map ((ME.calculus true).reduction.map eR.hom ≫
        pullbackReduction l E W ME f K)) ≫
      scalarPullbackRoosCoordinate l E L ι f P C (ME.calculus false) ρ K eP eC q =
    (integralOrdinaryDerivedScalar l E L ι (W true)).map eR.hom ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullback.{u, u} l E f).map eP.inv) ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullbackComparison.{u, u} l E f).hom.app P) ≫
      (integralOrdinaryScalar l E L ι (W true)).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor.{u, u} l E f).obj P.obj) ≫
      DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj) := by
  sorry

end WeilConjectures.ScalarExtensionTower
