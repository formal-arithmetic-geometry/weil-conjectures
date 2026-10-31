/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTowerSupplement
public import WeilConjectures.SixFunctors.CoefTowerTraceRectification

/-! # Unit-normalized derived point sections before limits

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
prop-coef-integral-dualizing.proof.md, paragraph 2; Stacks 0941 and 0D6E
(blueprint: def-coef-support-point-sections-data).

All categories are ordinary unbounded derived categories. Index n denotes exponent n+1.
The comparison and its evaluations are fixed by the canonical derived-unit equations.
-/

@[expose] public noncomputable section
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor




variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary completed-ring point sections with the structural constant R action.
Source: blueprint paragraph 2; node proof step 4
(blueprint: def-coef-support-point-sections-data). -/
abbrev ordinarySections (W : Scheme.{u}) :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (coefTraceConstantScalars l E W)) ⋙ (coefTraceSections l E W)

/-- Completed-ring point sections with strict R-module tower values; no limit.
Source: blueprint paragraph 2; node proof step 4
(blueprint: def-coef-support-point-sections-data). -/
def integralSections (W : Scheme.{u}) :=
  (ordinarySections l E W).rightDerivedFunctor

/-- K-injective resolutions on the actual quotient sequence ringed site.
Source: Stacks 079P; recorded ringed-site resolution theorem
(blueprint: def-coef-support-point-sections-data). -/
instance sequenceGrothendieck (W : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (coefficientSequenceModules.{u, u} l E W) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{
    u+1, u, u+1} (coefficientSequenceTopology (ProEt.topology W))
    (coefficientSequenceCommRingSheaf.{u, u} l E W)).1

/-- Ordinary quotient-system sections followed by integral scalar restriction.
Source: Stacks 0D6E; node proof step 4
(blueprint: def-coef-support-point-sections-data). -/
abbrev ordinaryQuotientSections (W : Scheme.{u}) :=
  coefTraceSystemRestriction l E W ⋙ coefTraceSections l E W

/-- Quotient-system point sections followed by exact integral scalar restriction.
This is derived sections on the quotient sequence topos with its R action.
Source: Stacks 0D6E; node proof step 4
(blueprint: def-coef-support-point-sections-data). -/
def quotientSections (W : Scheme.{u}) :=
  (ordinaryQuotientSections l E W).rightDerivedFunctor


/-- Ordinary sections of one completed module sheaf with its constant R action.
Source: blueprint paragraph 2; node proof step 4
(blueprint: def-coef-support-point-sections-data). -/
abbrev ordinaryLevelSections (W : Scheme.{u}) :=
  coefTraceConstantScalars l E W ⋙
    (sheafSections (ProEt.topology W) (ModuleCat.{u+1} (coefTraceRing l E))).obj
      (op (ProEt.mk (𝟙 W)))

/-- R-linear sections of one completed module sheaf, followed by total derivation.
This is the section functor on the one-point topos with its actual constant R action.
Source: blueprint paragraph 2; node proof step 4
(blueprint: def-coef-support-point-sections-data). -/
def levelSections (W : Scheme.{u}) :=
  (ordinaryLevelSections l E W).rightDerivedFunctor

/-- Canonical derived-unit normalization of the point-square comparison.
Source: Stacks 0D6E and 0941; blueprint paragraph 2, step 4
(blueprint: def-coef-support-point-sections-data). -/
def sectionsComparisonUnit (W : Scheme.{u})
    (comparison : quotientSections l E W ≅
      coefficientSequenceDerivedRestriction.{u, u} l E W ⋙ integralSections l E W) : Prop :=
  ∀ (C : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ),
    (ordinaryQuotientSections l E W).rightDerivedFunctorUnitQ C ≫
        comparison.hom.app (DerivedCategory.Q.obj C) =
      (ordinarySections l E W).rightDerivedFunctorUnitQ
          (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (integralSections l E W).map
          ((coefficientSequenceRestriction.{u, u} l E W).mapDerivedCategoryFactors.inv.app C)

/-- Canonical normalization of the evaluation comparison by derived units.
Source: Stacks 0D6E and 0941; blueprint paragraph 2, step 4
(blueprint: def-coef-support-point-sections-data). -/
def sectionsEvaluationUnit (W : Scheme.{u})
    (evaluation : ∀ n : ℕ,
    integralSections l E W ⋙ coefTraceEvaluation l E n ≅
      pbcTowerEvaluation W (completedIntegralCommRingSheafUnrestricted l E W) n ⋙
        levelSections l E W) : Prop :=
  ∀ (n : ℕ)
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ℤ),
    (coefTraceEvaluation l E n).map
        ((ordinarySections l E W).rightDerivedFunctorUnitQ C) ≫
        (evaluation n).hom.app (DerivedCategory.Q.obj C) ≫
        (levelSections l E W).map
          (((CategoryTheory.evaluation ℕᵒᵖ (scalarReductionSource.{u, u} l E W)).obj
            (op n)).mapDerivedCategoryFactors.hom.app C) =
      ((CategoryTheory.evaluation ℕᵒᵖ (ModuleCat.{u+1} (coefTraceRing l E))).obj
          (op n)).mapDerivedCategoryFactors.hom.app
            (((ordinarySections l E W).mapHomologicalComplex (.up ℤ)).obj C) ≫
        (ordinaryLevelSections l E W).rightDerivedFunctorUnitQ
          ((((CategoryTheory.evaluation ℕᵒᵖ (scalarReductionSource.{u, u} l E W)).obj
            (op n)).mapHomologicalComplex (.up ℤ)).obj C)

/-- The actual all-pair transition square for point-sections evaluation.
Source: Stacks 0D6E and 0941; blueprint paragraph 2, step 4
(blueprint: def-coef-support-point-sections-data). -/
def sectionsEvaluationTransitions (W : Scheme.{u})
    (evaluation : ∀ n : ℕ,
    integralSections l E W ⋙ coefTraceEvaluation l E n ≅
      pbcTowerEvaluation W (completedIntegralCommRingSheafUnrestricted l E W) n ⋙
        levelSections l E W) : Prop :=
  ∀ (C : coefficientSequenceRestrictedDerived.{u, u} l E W)
    (m n : ℕ) (h : n ≤ m),
    (coefTraceTransition l E h).app ((integralSections l E W).obj C) ≫
        (evaluation n).hom.app C =
      (evaluation m).hom.app C ≫ (levelSections l E W).map
        ((pbcTowerTransition W (completedIntegralCommRingSheafUnrestricted l E W) m n h).app C)

/-- Canonical composition and evaluation of point sections, before any inverse limit.
The unit equation fixes the restriction comparison on the whole derived sequence site.
Source: Stacks 0D6E, 0941; node proof step 4
(blueprint: def-coef-support-point-sections-data). -/
structure SectionsModel (W : Scheme.{u}) where
  comparison : quotientSections l E W ≅
    coefficientSequenceDerivedRestriction.{u, u} l E W ⋙ integralSections l E W
  comparison_unit : sectionsComparisonUnit l E W comparison
  evaluation : ∀ n : ℕ,
    integralSections l E W ⋙ coefTraceEvaluation l E n ≅
      pbcTowerEvaluation W (completedIntegralCommRingSheafUnrestricted l E W) n ⋙
        levelSections l E W
  evaluation_unit : sectionsEvaluationUnit l E W evaluation
  transitions : sectionsEvaluationTransitions l E W evaluation


end WeilConjectures.CoefSupportOpenTensor
