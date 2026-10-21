/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CompletedLineTensorCoherence
public import Sheaf.Paper.QuotientSystemMixedCoherence

/-! # Scalar model normalization before inverting completion

Source: Bhatt--Scholze, Definition 3.4.10 and Proposition 3.5.1;
Stacks Project, Tags 06YY and 0941.
(blueprint: lem-trf-scalar-model-associativity)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] F)
  (X : Scheme.{u})

/-- Ordinary scalar associativity commutes with quotient-normalized realization,
before any completion map is inverted. This holds on the ambient derived category.
Source: Bhatt--Scholze, Definition 3.4.10, Proposition 3.5.1 and Lemma 3.5.7;
Stacks 06YY, 0941, the scalar calculation in steps 8--10 of the parent.
(blueprint: lem-trf-scalar-model-associativity)

Proof: take a flat-term K-flat complex representing K, and a simultaneous strict
quotient presentation for its reduction. The three scalar-model normalizations
identify their realization maps with the Roos maps of the actual quotient tensors.
The initial completion maps have the quotient tensor maps in their unshifted
coordinates and zero shifted coordinates, by quotient_scalar_comparison_descent.
Use integralConeCounitRealization to replace insertion of the whole-system counit
by the original compatible family of quotient maps. The adjuncts of both displayed
arrows then have, at each quotient, the same map on generators:
c tensor (b tensor (a tensor x)) maps to c*j(b)*j(iota(a)) tensor x.
Balancing gives equality on all sections; sheafification preserves it. Multiplication
commutes with quotient transitions, restrictions, and the cochain differential.
Thus this is equality of strict diagram morphisms before localization. The universal
cochain counits identify their localizations with the specified ordinary and system
associators. The adjunction Hom bijection gives the displayed equality. Naturality
and K-flat resolutions transport it to arbitrary K. No separate evaluation functor
is assumed faithful, and no completion chain map is inverted. -/
theorem scalarModelAssociativity
    (SE : CoefficientDerivedSystemCalculus l E X)
    (SL : CoefficientDerivedSystemCalculus l L X)
    (ρL : IntegralComparisonRoosModel l L X)
    (ρF : IntegralComparisonRoosModel l F X)
    (bEL : IntegralComparisonScalarModel l E L ι X SE ρL)
    (bLF : IntegralComparisonScalarModel l L F j X SL ρF)
    (bEF : IntegralComparisonScalarModel l E F (j.comp ι) X SE ρF)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (completedDerivedScalarExtension l L F j X).map
        ((completedScalarComparison l E L ι X).app K) ≫
      (completedScalarComparison l L F j X).app
        ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≫
      (integralScalarExtensionOfUniverses l L F j X).map (bEL.realization.hom.app K) ≫
      bLF.realization.hom.app
        ((coefficientSequenceLimit l L X).obj
          ((integralComparisonDerivedSequenceScalar l E L ι X).obj (SE.reduction.obj K))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonDerivedSequenceScalar l L F j X).map
          (SL.adjunction.counit.app
            ((integralComparisonDerivedSequenceScalar l E L ι X).obj (SE.reduction.obj K)))) ≫
      (coefficientSequenceLimit l F X).map
        ((integralComparisonSystemScalarComposition l E L F ι j X).hom.app
          (SE.reduction.obj K)) =
    (CompletedLineTensor.associatorData l E X L ι F j).derived.hom.app K ≫
      (completedScalarComparison l E F (j.comp ι) X).app K ≫ bEF.realization.hom.app K := by
  sorry

end WeilConjectures
