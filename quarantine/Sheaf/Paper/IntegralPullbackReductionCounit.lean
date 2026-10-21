/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.IntegralTowerInverseImageUnit
public import Sheaf.Paper.IntegralPullbackComparisonRealization

/-!
# The reduction-unit computation of the integral inverse-image comparison

Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tags 06YY and 0941.
(blueprint: lem-trf-integral-pullback-reduction-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- The counit image of the defining Roos lift is the inverse image of the
whole-system reduction unit, followed by the finite tensor unit. This is the
reduction-unit computation, before composing with a map from the reduction to
any other quotient system. It is stated only on a flat-term K-flat complex,
before any resolution is inverted.

Source: Bhatt--Scholze, Lemma 6.5.9(4); Stacks Project, Tags 06YY and 0941;
Steps 1, 3 and 5 of the resolution-matching argument
(blueprint: lem-trf-integral-pullback-reduction-counit).

Proof: the reduction model of S supplies a
single strict quotient system B representing S.reduction(Q(P)). On the small
sequence site, extension from the diagonal completed ring is left adjoint to
exact restriction. The derived unit on the K-flat diagonal P is the strict
quotient map r:Delta(P) to U(B). Under the composite diagonal/limit and
extension/restriction adjunction this is
Delta(S.adjunction.unit) followed by the diagonal/limit counit. The uniqueness
of left adjoints, expressed by integralComparisonReductionFactor, identifies
this computation with the recorded S.adjunction. The simultaneous presentation
normalization of F identifies its realization with the Roos complex of h-star B.
The generator equations of this normalization and integralTowerInverseImageUnit
identify the family theta defining kappa with H(r) followed by the finite unit.
The K-injective normalization of rho and integralComparisonTowerCounit_computes
identify the two derived-limit counits. Apply integralConeCounitRealization to
theta, then transport along the tower presentation and the exact-derived
comparison for inverse image. This gives the displayed identity in the derived
category of whole towers. No equality is detected merely by evaluation at finite levels. -/
theorem integralPullbackKFlatReductionCounit
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (S : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E Z)
    (F : IntegralComparisonPullbackModel l E h S ρ)
    (P : (integralOperationsGoodComplex l E W).FullSubcategory) :
    (integralComparisonConstantTower l E Z).map
        ((inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
          (integralDerivedPullbackComparison l E h).inv.app P ≫
          F.realization.hom.app (DerivedCategory.Q.obj P.obj)) ≫
        (integralComparisonTowerCounit l E Z).app
          ((coefficientSequenceDerivedRestriction l E Z).obj
            ((integralComparisonDerivedSequencePullback l E h).obj
              (S.reduction.obj (DerivedCategory.Q.obj P.obj)))) =
      (integralTowerInverseImageDiagonal l E h).hom.app (DerivedCategory.Q.obj P.obj) ≫
        (integralDerivedTowerInverseImage l E h).map
          ((integralComparisonConstantTower l E W).map
              (S.adjunction.unit.app (DerivedCategory.Q.obj P.obj)) ≫
            (integralComparisonTowerCounit l E W).app
              ((coefficientSequenceDerivedRestriction l E W).obj
                (S.reduction.obj (DerivedCategory.Q.obj P.obj)))) ≫
        (integralDerivedTowerInverseImageUnit l E h).hom.app
          (S.reduction.obj (DerivedCategory.Q.obj P.obj)) := by
  sorry

end WeilConjectures
