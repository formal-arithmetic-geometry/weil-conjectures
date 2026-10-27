/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels

/-! # The finite component of a strict normalized pullback comparison

Source: Stacks Tags 03D3, 099N(5), and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
  WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.coefficientFiniteDerivedRestriction
  WeilConjectures.coefficientConstantTowerEvaluation
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

/-- The finite component of a strict tower comparison is fixed by its values on
inverse-image unit generators. This is a statement about the strict comparison q;
it has no integral realization or reduction/limit counit as an input.
Source: Stacks 03D3 (inverse-image adjunction), 099N(5), and 0941;
step 1 of lem-pod-integral-pullback-counit-projection.
(blueprint: lem-pod-integral-pullback-strict-finite-component).

Proof: evaluate the system inverse-image unit at level n. The defining property of
finiteSystemPullbackEvaluation identifies it with the ordinary finite inverse-image
unit. The defining property of integralFinitePullbackModel identifies the other
presentation with this same unit. After transporting by kappa, the hypothesis says
that both maps have the same values on these unit sections. The completed-to-finite
coefficient projection is locally surjective; thus completed-linear maps between
these restricted quotient modules are already quotient-linear. The inverse-image
adjunction, or equivalently its locally generating unit sections and scalar multiples,
therefore makes the two maps equal in every degree. The degreewise equalities commute
with the differentials. Apply Q, and use the exact-functor factorization comparisons
for restriction, evaluation and inverse image. This gives precisely the displayed
identity. The proof uses no flatness of a transition map, no effectivity, and no
invertibility of a derived reduction counit. It also covers zero complexes, empty
schemes, and n=0, where the coefficient exponent is one. -/
theorem integralPullbackStrictFiniteComponent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
      ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj U))
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj (C.X i)) n
          (op ((proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
          (((κ n).hom.f i).val.app (op U)
            (coefficientEvaluationSection l E Y (C.X i) n (op U) x))) (n : ℕ) :
    (integralComparisonRestrictedEvaluationFactors l E X
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C)
      n).hom ≫
      DerivedCategory.Q.map (q.hom.app (op n)) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj
          ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
            (.up ℤ)).hom.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) ≫
          (proEtaleConstantRingPullback
            (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.inv.app
            ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) =
    (coefficientFiniteDerivedRestriction l E X n).map
      ((coefficientSequenceDerivedEvaluation l E X n).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.inv.app C) ≫
        (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) f n).hom.app (DerivedCategory.Q.obj C) ≫
        (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
            DerivedCategory.Q.map (κ n).hom)) := by sorry

end WeilConjectures
