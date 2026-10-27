/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.ExactProductFunctorStrictLimit

/-! # Multiplication and product comparison on entire strict quotient cones

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, (2)--(3); Stacks Tags 0941 and 08TC
(blueprint: def-trf-isomorphism-strict-quotient-models).

The positive exponent is n+1. The finite pullbacks and quotient transitions are the
published strict constructions. Multiplication is specified on their sheafified
unit generators; bundled linearity gives all scalar multiples. The two existing
mapping-cocone projections specify the product comparison on both coordinates,
including zero off-diagonal entries. The completion comparison is normalized on
every simultaneous quotient presentation through the existing K-injective-normalized Roos model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance 3000] integralTowerHasDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

/-- The actual strict quotient tower D, functorial in the original complex.
Source: blueprint rational-frobenius-integral-model (2); Stacks 06YY and 0941
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
def trfQuotientTowerFunctor (W : Scheme.{t}) :
    CochainComplex (integralTowerModules l E W) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
    (unrestrictedIntegralTransition l E W)).flip

/-- Termwise completed inverse image, with scalar action through c inverse.
Source: blueprint rational-frobenius-integral-model (2); Stacks 03D6
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfInverseImageComplex {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)

/-- Postcomposition on strict towers, retaining their transition maps.
Source: blueprint rational-frobenius-integral-model (2); Stacks 0941
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfInverseImageTower {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  (Functor.whiskeringRight ℕᵒᵖ
    (CochainComplex (integralTowerModules l E Y) ℤ)
    (CochainComplex (integralTowerModules l E X) ℤ)).obj (trfInverseImageComplex l E g)

/-- The existing difference 1-s on the product of the quotient tower D(Q).
Source: blueprint rational-frobenius-integral-model (2); Stacks 08TC
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfQuotientDifference (W : Scheme.{t})
    (Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((trfQuotientTowerFunctor l E W).obj Q).obj (op n))
    (integralOperationsTowerStep ((trfQuotientTowerFunctor l E W).obj Q))

/-- The same difference on GD(Q), with the actual inverse-image transitions.
Source: blueprint rational-frobenius-integral-model (2); Stacks 08TC
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfInverseQuotientDifference {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((trfInverseImageTower l E g).obj
      ((trfQuotientTowerFunctor l E Y).obj Q)).obj (op n))
    (integralOperationsTowerStep
      ((trfInverseImageTower l E g).obj ((trfQuotientTowerFunctor l E Y).obj Q)))

/-- The canonical product arrow phi, characterized by its product projections.
Source: blueprint rational-frobenius-integral-model (2); Stacks 0941
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
@[reducible]
def trfQuotientProductComparison {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :=
  piComparison (trfInverseImageComplex l E g)
    (fun n : ℕ ↦ ((trfQuotientTowerFunctor l E Y).obj Q).obj (op n))

attribute [local irreducible] integralOperationsRoos

/-- The normalized representative comparison for L R. It tests whole strict quotient
adjunction-coherent presentations. The whole-system adjunction coherence fixes e
before taking a limit.
The section formula fixes the strict tower identification a to the actual finite
comparison kappa. The final
formula is its total-limit/Roos realization, including the specified comparison e.
Source: blueprint rational-frobenius-integral-model (2)--(3); Stacks 06YY and 0941
(blueprint: def-trf-isomorphism-strict-quotient-models). -/
def TrfCompletionRoosNormalized (W : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E W)
    (r : IntegralComparisonRoosModel l E W)
    (rho : integralOperationsGoodLocalization l E W ⋙
        (S.reduction ⋙ coefficientSequenceLimit l E W) ≅
      (integralOperationsGoodComplex l E W).ι ⋙ trfQuotientTowerFunctor l E W ⋙
        integralOperationsRoosFunctor ⋙ DerivedCategory.Q) : Prop :=
  ∀ (P : (integralOperationsGoodComplex l E W).FullSubcategory)
    (K : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj K)
    (kappa : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj K ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P.obj),
    CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 K e kappa →
    IsIntegralComparisonPresentationCoherent l E W S P.obj K e kappa →
    ∃ a : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
        K).asFunctor ≅ (trfQuotientTowerFunctor l E W).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (K.X i).val.obj (op (n, U.unop))),
        ((a.hom.app (op n)).f i).val.app U
            (integralComparisonRestrictedSection l E W (K.X i) n U x) =
          ((kappa n).hom.f i).val.app U
            (coefficientEvaluationSection l E W (K.X i) n U x)) ∧
      rho.hom.app P =
        (coefficientSequenceLimit l E W).map e.hom ≫
          (integralComparisonRoosBridge l E W r K).hom ≫
            DerivedCategory.Q.map (integralOperationsRoosFunctor.map a.hom)

attribute [local semireducible] integralOperationsRoos

end WeilConjectures
