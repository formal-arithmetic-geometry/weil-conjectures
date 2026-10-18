/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Mathlib.CategoryTheory.Whiskering
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic

/-!
# Realization of integral pullback comparisons

Source: Stacks Project, Tags 099N(2),(5), 0D6D, 06YY and 0941; blueprint
`sec-trace-formula/sk-thm-trace-transport/prop-trf-karoubi-independence.proof.md`,
final common-stage transport paragraph
(blueprint: def-trf-integral-comparison-realization-models).

The sequence site retains the whole quotient diagram. Its pullback is the left
adjoint of the actual sectionwise direct image. Scalar change is the universal
derived change of rings for the actual map of quotient coefficient sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

variable (X : Scheme.{t})

/-- The exact constant tower functor, on ordinary derived categories.
Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonConstantTower :
    DerivedCategory (scalarReductionSource l E X) ⥤
      coefficientSequenceRestrictedDerived l E X :=
  (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
    ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategory

/-- The exact diagonal/total-limit adjunction, using the ordinary adjunction
and the universal right derived functor. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonConstantAdjunction : integralComparisonConstantTower l E X ⊣
    coefficientConstantTowerLimit l E X :=
  (constLimAdj (J := ℕᵒᵖ)
    (C := scalarReductionSource l E X)).mapDerivedCategoryRightDerivedAdjunction

/-- The counit in the derived category of whole strict towers.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonTowerCounit :
    coefficientConstantTowerLimit l E X ⋙ integralComparisonConstantTower l E X ⟶ 𝟭 _ :=
  (integralComparisonConstantAdjunction l E X).counit

/-- On a simultaneous K-injective resolution this is the ordinary limit cone.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models).
Proof: the universal derived adjunction evaluates on a K-injective complex by
the right-derived comparison. Its underlying ordinary adjunction counit is
exactly the constant limit cone, giving the displayed formula. Naturality
transports this formula along every K-injective resolution. -/
theorem integralComparisonTowerCounit_computes :
     ∀ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
      [I.IsKInjective],
    (integralComparisonTowerCounit l E X).app (DerivedCategory.Q.obj I) =
      (integralComparisonConstantTower l E X).map
        (Functor.rightDerivedFunctorObjQIso
          (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ scalarReductionSource l E X) I).hom ≫
      (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤
        ℕᵒᵖ ⥤ scalarReductionSource l E X).mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
            scalarReductionSource l E X).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (constLimAdj (J := ℕᵒᵖ) (C := scalarReductionSource l E X)).counit
          (ComplexShape.up ℤ)).app I) := by
  sorry

/-- Whole-diagram coefficient restriction has derived scalar extension as
left adjoint. Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-realization-models).
Proof: realize towers as modules over the horizontal-constant completed ring on
the sequence site. The actual quotient ring sheaf map gives ordinary extension
left adjoint to restriction. K-flat resolutions derive this adjunction, because
restriction is exact. The right functor is precisely the recorded derived
coefficientSequenceRestriction, with its unchanged section maps. -/
theorem integralComparisonSystemRestriction_isRightAdjoint :
    (coefficientSequenceDerivedRestriction l E X).IsRightAdjoint := by
  sorry

/-- The actual whole-system extension/restriction adjunction.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-realization-models). -/
instance integralComparisonSystemRestrictionRightAdjoint :
    (coefficientSequenceDerivedRestriction l E X).IsRightAdjoint :=
  integralComparisonSystemRestriction_isRightAdjoint l E X

/-- Derived quotient-module extension on the entire tower category.
Source: Stacks 06YY (blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonSystemExtension :=
  (coefficientSequenceDerivedRestriction l E X).leftAdjoint

/-- The unique adjunction-compatible comparison of reduction with constant-tower
extension. Its mate is the identity of the actual total-limit functor.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonReductionFactor (S : CoefficientDerivedSystemCalculus l E X) :
    integralComparisonConstantTower l E X ⋙ integralComparisonSystemExtension l E X ≅
      S.reduction :=
  ((integralComparisonConstantAdjunction l E X).comp
    (Adjunction.ofIsRightAdjoint
      (coefficientSequenceDerivedRestriction l E X))).leftAdjointUniq S.adjunction

/-- Reduction's counit is obtained by applying whole-diagram coefficient change
to epsilon and then the quotient-module action counit.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-realization-models).
Proof: expand leftAdjointUniq and the composite adjunction counit. Its counit is
extension of the diagonal-limit counit followed by the extension/restriction
counit. The mate-identity equation cancels the comparison and gives the formula.
Thus this is an equality in the whole diagram derived category. -/
theorem integralComparisonReductionCounit_formula
    (S : CoefficientDerivedSystemCalculus l E X) (N : coefficientSequenceDerived l E X) :
    S.adjunction.counit.app N =
      (integralComparisonReductionFactor l E X S).inv.app
        ((coefficientSequenceLimit l E X).obj N) ≫
      (integralComparisonSystemExtension l E X).map
        ((integralComparisonTowerCounit l E X).app
          ((coefficientSequenceDerivedRestriction l E X).obj N)) ≫
      (Adjunction.ofIsRightAdjoint
        (coefficientSequenceDerivedRestriction l E X)).counit.app N := by
  sorry

/-- The ordinary limit maps to its Roos cocone by the limit tuple and zero in
its shifted coordinate. Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models).
Proof: the compatible limit tuple is killed by 1-s, so the two indicated
coordinates commute with the signed cocone differential. They give a chain map.
The two cocone coordinates jointly determine that map, proving uniqueness. -/
theorem integralComparisonLimitToRoos_existsUnique
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :
    ∃! α : ((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤
        scalarReductionSource l E X).mapHomologicalComplex (ComplexShape.up ℤ)).obj C ⟶
      integralOperationsRoos C.asFunctor,
      (∀ n : ℕ, α ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary C.asFunctor) ≫ Pi.π (fun m ↦ C.asFunctor.obj (op m)) n =
        (NatTrans.mapHomologicalComplex (lim.π (op n)) (ComplexShape.up ℤ)).app C) ∧
      (∀ (i j : ℤ) (h : i + -1 = j), α.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary C.asFunctor)).v i j h = 0) := by
  sorry

/-- The specified limit-tuple/zero-shifted-coordinate map.
Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonLimitToRoos
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ) :=
  (integralComparisonLimitToRoos_existsUnique l E X C).exists.choose

/-- The Roos model of total limit, with its exact K-injective normalization.
Source: Stacks 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
structure IntegralComparisonRoosModel where
  /-- A natural comparison on entire strict tower complexes. -/
  comparison : DerivedCategory.Q ⋙ coefficientConstantTowerLimit l E X ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  /-- It is induced on simultaneous K-injectives by the ordinary limit cone. -/
  computes : ∀ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E X) ℤ)
      [I.IsKInjective],
    comparison.hom.app I =
      (Functor.rightDerivedFunctorObjQIso
        (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E X) ⥤ scalarReductionSource l E X) I).hom ≫
      DerivedCategory.Q.map (integralComparisonLimitToRoos l E X I)

/-- Scalar restriction has exactly the original underlying section type.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models).
Proof: the object equation for coefficientSequenceRestriction identifies it with
ordinary finite restriction after evaluation. Neither restriction changes the
underlying abelian sheaf, and coefficientSequenceEvaluationAb_eq finishes. -/
theorem integralComparisonRestrictedSectionType (M : coefficientSequenceModules l E X)
    (n : ℕ) (U : X.ProEtᵒᵖ) :
    ↥((((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.obj U) =
      ↥(M.val.obj (op (n, U.unop))) := by
  sorry

/-- The same section read over the completed coefficient sheaf.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonRestrictedSection (M : coefficientSequenceModules l E X)
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.obj U :=
  cast (integralComparisonRestrictedSectionType l E X M n U).symm x

/-- The inverse identification of evaluation sections with original sections.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonSequenceSection (M : coefficientSequenceModules l E X)
    (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E X n).obj M).val.obj U) :
    M.val.obj (op (n, U.unop)) :=
  (eqToHom (coefficientSequenceEvaluationAb_eq l E X M n U)) x

/-- The normalized passage from the derived total limit to the actual Roos cocone.
Source: Stacks 0941 (blueprint: def-trf-integral-comparison-realization-models). -/
def integralComparisonRoosBridge (ρ : IntegralComparisonRoosModel l E X)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ) :
    (coefficientSequenceLimit l E X).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (integralOperationsRoos
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C).asFunctor) :=
  (coefficientConstantTowerLimit l E X).mapIso
    ((coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.app C) ≪≫
    ρ.comparison.app
      (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj C)

/-- The representative normalization of completed pullback, expressed as one named
predicate so that the model structure does not repeatedly elaborate the long equation.
Source: Stacks 099N(5), 0D6D, 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def IsIntegralComparisonPullbackNormalized {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E Z)
    (realization : integralDerivedPullback l E f ≅ S.reduction ⋙
      integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E Z) :
    Prop :=
  ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P.obj),
    CoefficientReductionPresentation l E Y S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    ∃ q : (((coefficientSequenceRestriction l E Z).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
        ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj U))
          (integralComparisonRestrictedSection l E Z
            ((integralComparisonSequencePullback l E f).obj (C.X i)) n
            (op ((proEtaleBaseChange f).obj U))
            (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
          integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X i) U
            (((κ n).hom.f i).val.app (op U)
              (coefficientEvaluationSection l E Y (C.X i) n (op U) x))) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonDerivedSequencePullback l E f).map e.hom) ≫
        (coefficientSequenceLimit l E Z).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
        (integralComparisonRoosBridge l E Z ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralDerivedPullbackComparison l E f).hom.app P

/-- The completed pullback is the total limit of the actual finite pullback of
one reduction diagram. The normalization tests every simultaneous presentation
of every flat-term K-flat complex, and fixes maps on tensor-unit generators.
Source: Stacks 099N(5), 0D6D, 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
structure IntegralComparisonPullbackModel {Y Z : Scheme.{t}} (f : Z ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Y)
    (ρ : IntegralComparisonRoosModel l E Z) where
  /-- Natural realization on the ambient derived category. -/
  realization : integralDerivedPullback l E f ≅ S.reduction ⋙
    integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceLimit l E Z
  /-- On every representative it is the defining pullback tower comparison. -/
  normalization : IsIntegralComparisonPullbackNormalized l E f S ρ realization

/-- The same simultaneous quotient-presentation normalization for completed scalar change.
Naming this predicate preserves the equation while keeping model projections small.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
def IsIntegralComparisonScalarNormalized
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X)
    (realization : integralScalarExtensionOfUniverses l E L ι X ≅ S.reduction ⋙
      integralComparisonDerivedSequenceScalar l E L ι X ⋙ coefficientSequenceLimit l L X) :
    Prop :=
  ∀ (P : (integralOperationsGoodComplex l E X).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (e : S.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E X n).obj P.obj),
    CoefficientReductionPresentation l E X S.toCoefficientDerivedSystemReduction
      P.obj P.property.1 C e κ →
    ∃ q : (((coefficientSequenceRestriction l L X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel l E L ι X).E.mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅ (integralScalarTowerFunctor l E L ι X).obj P.obj,
      (∀ (n : ℕ) (i : ℤ) (U : X.ProEtᵒᵖ)
        (s : (coefficientSequenceCommRingSheaf l L X).obj.obj (op (n, U.unop)))
        (x : (P.obj.X i).val.obj U),
        ((q.hom.app (op n)).f i).val.app U
          (integralComparisonRestrictedSection l L X
            ((integralComparisonSequenceScalarModel l E L ι X).E.obj (C.X i)) n U
            (integralComparisonSequenceTensorSection l E L ι X (C.X i)
              (op (n, U.unop)) s
              (integralComparisonSequenceSection l E X (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E X n (P.obj.X i) U 1 x))))) =
          integralScalarTensorSection l E L ι X n (P.obj.X i) U s x) ∧
      realization.hom.app (DerivedCategory.Q.obj P.obj) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonDerivedSequenceScalar l E L ι X).map e.hom) ≫
        (coefficientSequenceLimit l L X).map
          ((integralComparisonSequenceScalarModel l E L ι X).ε.app C) ≫
        (integralComparisonRoosBridge l L X ρ _).hom ≫
        DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom) =
          (integralScalarExtensionComparisonOfUniverses l E L ι X).hom.app P

/-- Scalar realization uses the very same reduction diagram and the universal
cochain counit of actual change of rings on that diagram.
Source: Stacks 06YY, 0941
(blueprint: def-trf-integral-comparison-realization-models). -/
structure IntegralComparisonScalarModel
    (S : CoefficientDerivedSystemCalculus l E X)
    (ρ : IntegralComparisonRoosModel l L X) where
  /-- Completed scalar extension as realization of whole-system scalar change. -/
  realization : integralScalarExtensionOfUniverses l E L ι X ≅ S.reduction ⋙
    integralComparisonDerivedSequenceScalar l E L ι X ⋙ coefficientSequenceLimit l L X
  /-- The fixed quotient-map/zero-shifted-coordinate representative normalization. -/
  normalization : IsIntegralComparisonScalarNormalized l E L ι X S ρ realization


end WeilConjectures
