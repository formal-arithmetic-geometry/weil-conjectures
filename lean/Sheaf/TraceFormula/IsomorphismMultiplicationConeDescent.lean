/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.CategoryTheory.StrictRoosComparison
public import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

/-! # Multiplication and product comparison on entire strict quotient cones

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, (2)--(3); Stacks Tags 0941 and 08TC
(blueprint: lem-trf-isomorphism-multiplication-cone-descent).

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

/-- The actual strict quotient tower D, functorial in the original complex.
Source: blueprint rational-frobenius-integral-model (2); Stacks 06YY and 0941
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
def trfQuotientTowerFunctor (W : Scheme.{t}) :
    CochainComplex (integralTowerModules l E W) ℤ ⥤
      ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ :=
  (Functor.ofOpSequence (X := fun n ↦ unrestrictedIntegralComplexFunctor l E W n)
    (unrestrictedIntegralTransition l E W)).flip

/-- Termwise completed inverse image, with scalar action through c inverse.
Source: blueprint rational-frobenius-integral-model (2); Stacks 03D6
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfInverseImageComplex {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  (inverseImageIntegralModules l E g).mapHomologicalComplex (.up ℤ)

/-- Postcomposition on strict towers, retaining their transition maps.
Source: blueprint rational-frobenius-integral-model (2); Stacks 0941
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfInverseImageTower {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :=
  (Functor.whiskeringRight ℕᵒᵖ
    (CochainComplex (integralTowerModules l E Y) ℤ)
    (CochainComplex (integralTowerModules l E X) ℤ)).obj (trfInverseImageComplex l E g)

/-- The existing difference 1-s on the product of the quotient tower D(Q).
Source: blueprint rational-frobenius-integral-model (2); Stacks 08TC
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfQuotientDifference (W : Scheme.{t})
    (Q : CochainComplex (integralTowerModules l E W) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((trfQuotientTowerFunctor l E W).obj Q).obj (op n))
    (integralOperationsTowerStep ((trfQuotientTowerFunctor l E W).obj Q))

/-- The same difference on GD(Q), with the actual inverse-image transitions.
Source: blueprint rational-frobenius-integral-model (2); Stacks 08TC
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfInverseQuotientDifference {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :=
  towerTransitionEndomorphism
    (K := fun n : ℕ ↦ ((trfInverseImageTower l E g).obj
      ((trfQuotientTowerFunctor l E Y).obj Q)).obj (op n))
    (integralOperationsTowerStep
      ((trfInverseImageTower l E g).obj ((trfQuotientTowerFunctor l E Y).obj Q)))

/-- The canonical product arrow phi, characterized by its product projections.
Source: blueprint rational-frobenius-integral-model (2); Stacks 0941
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
abbrev trfQuotientProductComparison {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (Q : CochainComplex (integralTowerModules l E Y) ℤ) :=
  piComparison (trfInverseImageComplex l E g)
    (fun n : ℕ ↦ ((trfQuotientTowerFunctor l E Y).obj Q).obj (op n))

attribute [local irreducible] integralOperationsRoos

/-- The normalized representative comparison for L R. It tests whole strict quotient
presentations, not only their derived evaluations. The section formula fixes the
strict tower identification a to the actual finite comparison kappa. The final
formula is its total-limit/Roos realization, including the specified comparison e.
Source: blueprint rational-frobenius-integral-model (2)--(3); Stacks 06YY and 0941
(blueprint: lem-trf-isomorphism-multiplication-cone-descent). -/
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

/-- Multiplication and the canonical product comparison give the same natural
isomorphism on all strict quotient cones and after localization.

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md (2)--(3); Stacks 0941 and 08TC
(blueprint: lem-trf-isomorphism-multiplication-cone-descent).

Proof, following the ten steps of the node:
1. The site equivalence identifies inverse-image sections with sections after
postcomposition by g. Transport through c inverse preserves addition, kernels,
cokernels and sectionwise products. Product projections fix phi and its inverse.
2. Resolve by one flat-term K-flat Q. The derived-system evaluation calculus gives
its entire strict quotient system. The ambient pullback is H(C), and normalized
strict Roos comparison identifies L R with H(D), without completeness or bounds.
3. Scalar extension through c_n has multiplication inverse to x to x tensor 1.
The completed projection equation proves completed linearity. Both composites
are identities by the tensor balancing relation, also after sheafification.
4. The actual quotient transition sends x tensor a to tau(x) tensor reduction(a).
The coefficient square shows multiplication commutes with this map. Restrictions,
differentials and arbitrary chain maps satisfy the same generator identities.
5. Product projections give phi G(s)=s phi and hence the difference square.
Apply phi to both coordinates of the shifted cone. Its differential is
(-db-(1-s)a,da), so this is an invertible chain map with no cross terms. The
exact-product derived-limit comparison gives this same map under normalized Roos
identifications: (b,a) to (a,-b) converts its signed-coordinate convention.
6. Apply H to the strict multiplication isomorphism and follow by eta inverse.
Products and cone coordinates prove naturality of this entire chain isomorphism.
7. A homotopy h acts on reductions and their products, commuting with the quotient
shift. On the cone its homotopy is (-h,h); the cross term h(1-s)-(1-s)h vanishes.
Thus both constructions and their natural isomorphism respect homotopies.
8. The ambient-operation well-definedness theorem inverts quasi-isomorphisms on
good representatives. On the other side, reduction, strict Roos localization and
exact inverse image invert them too. Their normalized comparisons are functorial.
9. The resolving-class localization theorem extends the strict natural isomorphism
and its inverse uniquely to the ordinary unbounded derived category. Uniqueness
makes both composites identity and proves naturality on every derived morphism.
10. The representative equation below holds after every isomorphism Q(P) to N.
Consequently every allowed resolution gives this same component through its
canonical comparisons. No completeness, constructibility or boundedness is used. -/
theorem isomorphismMultiplicationConeDescent
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : CoefficientDerivedSystemCalculus l E Y)
    (r : IntegralComparisonRoosModel l E Y) :
    (inverseImageIntegralModules l E g).Additive ∧
    PreservesFiniteLimits (inverseImageIntegralModules l E g) ∧
    PreservesFiniteColimits (inverseImageIntegralModules l E g) ∧
    (∀ Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
      IsIso (trfQuotientProductComparison l E g Q.obj)) ∧
    ∃ (j : (integralOperationsGoodComplex l E Y).ι ⋙
          integralOperationsPullbackTowerFunctor l E g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙
          trfQuotientTowerFunctor l E Y ⋙ trfInverseImageTower l E g)
      (eta : (integralOperationsGoodComplex l E Y).ι ⋙
          trfQuotientTowerFunctor l E Y ⋙ integralOperationsRoosFunctor ⋙
            trfInverseImageComplex l E g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ trfQuotientTowerFunctor l E Y ⋙
          trfInverseImageTower l E g ⋙ integralOperationsRoosFunctor)
      (rho : integralOperationsGoodLocalization l E Y ⋙
          (S.reduction ⋙ coefficientSequenceLimit l E Y) ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ trfQuotientTowerFunctor l E Y ⋙
          integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
      (Theta : integralDerivedPullback l E g ≅
        (S.reduction ⋙ coefficientSequenceLimit l E Y) ⋙ inverseImageIntegralDerived l E g),
      -- The unit-generator equation and bundled linearity specify multiplication.
      (∀ (Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) (i : ℤ)
        (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (((j.hom.app Q).app (op n)).f i).val.app (op U)
            ((((integralOperationsPullbackLevel l E g n).obj Q.obj).X i).val.map
              (proEtaleIsoCommaArrow g U).op
              (integralOperationsPullbackGenerator l E g n
                (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i)
                ((proEtaleIsoPostcompose g).obj U) x)) = x) ∧
      -- The inverse is the actual sheafified x to x tensor 1 map.
      (∀ (Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) (i : ℤ)
        (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (((j.inv.app Q).app (op n)).f i).val.app (op U) x =
          ((((integralOperationsPullbackLevel l E g n).obj Q.obj).X i).val.map
            (proEtaleIsoCommaArrow g U).op
            (integralOperationsPullbackGenerator l E g n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i)
              ((proEtaleIsoPostcompose g).obj U) x))) ∧
      (∀ Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (trfInverseImageComplex l E g).map (trfQuotientDifference l E Y Q.obj) ≫
            trfQuotientProductComparison l E g Q.obj =
          trfQuotientProductComparison l E g Q.obj ≫ trfInverseQuotientDifference l E g Q.obj) ∧
      -- Equality on the a coordinate of H, as a chain map.
      (∀ Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        eta.hom.app Q ≫ CochainComplex.mappingCocone.fst
            (trfInverseQuotientDifference l E g Q.obj) =
          (trfInverseImageComplex l E g).map
              (CochainComplex.mappingCocone.fst (trfQuotientDifference l E Y Q.obj)) ≫
            trfQuotientProductComparison l E g Q.obj) ∧
      -- Equality on the shifted b coordinate; together these specify a diagonal map.
      (∀ (Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (p : ℤ),
        (eta.hom.app Q).f (p + 1) ≫
            (CochainComplex.mappingCocone.snd
              (trfInverseQuotientDifference l E g Q.obj)).v (p + 1) p
                (add_neg_cancel_right p 1) =
          (inverseImageIntegralModules l E g).map
              ((CochainComplex.mappingCocone.snd
                (trfQuotientDifference l E Y Q.obj)).v (p + 1) p
                  (add_neg_cancel_right p 1)) ≫
            (trfQuotientProductComparison l E g Q.obj).f p) ∧
      TrfCompletionRoosNormalized l E Y S r rho ∧
      -- The descended map is H(j) followed by eta inverse on every representative.
      (∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory),
        Theta.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (inverseImageIntegralDerived l E g).map (rho.hom.app P) ≫
            (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app
              (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P.obj)) =
          (integralDerivedPullbackComparison l E g).hom.app P ≫
            DerivedCategory.Q.map
              (integralOperationsRoosFunctor.map ((j.hom.app P)) ≫ eta.inv.app P)) ∧
      -- This equation includes every resolution and every derived object N.
      (∀ (N : DerivedCategory (integralTowerModules l E Y))
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ N),
        Theta.hom.app N =
          (integralDerivedPullback l E g).map e.inv ≫
            (integralDerivedPullbackComparison l E g).hom.app P ≫
            DerivedCategory.Q.map
              (integralOperationsRoosFunctor.map (j.hom.app P) ≫ eta.inv.app P) ≫
            (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.inv.app
              (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P.obj)) ≫
            (inverseImageIntegralDerived l E g).map (rho.inv.app P) ≫
            ((S.reduction ⋙ coefficientSequenceLimit l E Y) ⋙
              inverseImageIntegralDerived l E g).map e.hom) := by
  sorry

end WeilConjectures
