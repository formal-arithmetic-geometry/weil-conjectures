/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientDerivedSectionsCoreData

/-! Equations for the normalized coefficient-sections core data.
Source: Stacks 079P, 0941, 0D6E and 03CZ.
(blueprint: lem-coef-derived-sections-core-equations)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The resolution and projection equations for transported sections data.
Source: Stacks 079P, 0941 and 0D6E; the simultaneous sections/limit comparison
and its actual finite projections.
Proof: apply the normalized sections/limit comparison to the transported pairs,
then identify each derived projection with the prescribed coefficient projection by
uniqueness of the corresponding right-derived comparison. The universal-unit
identity gives the first clause, and the finite projection identity gives the second.
(blueprint: lem-coef-derived-sections-core-equations) -/
def CoefficientDerivedSectionsCoreResolutionEquation
    (R : CoefficientDerivedSystemReduction l E W)
    (D : CoefficientDerivedSectionsCoreData l E W R) : Prop :=
  ∀ (K : CochainComplex (coefficientSequenceModules l E W) ℤ),
    CoefficientComparisonEquation
      (coefficientGlobalLimitLeftComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      ((coefficientIntegralSections l E W).map
          ((coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))
      (D.globalLimit.hom.app (DerivedCategory.Q.obj K))
      (coefficientGlobalLimitRightComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      (coefficientMappingLimit.{max u (t + 1)}.map
        ((coefficientTowerSections l E W).rightDerivedFunctor.map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))

/-- The transported data satisfy their resolution and finite projection equations.
Source: Stacks 079P, 0941, 0D6E and 03CZ; extracted construction step of the
normalized coefficient-sections package.
(blueprint: lem-coef-derived-sections-core-equations) -/
theorem coefficientDerivedSectionsCoreEquations
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (D : CoefficientDerivedSectionsCoreData l E W R) :
    CoefficientDerivedSectionsCoreResolutionEquation l E W R D ∧
      (∀ (M : coefficientSequenceDerived l E W) (n : ℕ),
        D.globalLimit.hom.app M ≫
            (coefficientMappingProjection.{max u (t + 1)} n).app
              ((coefficientSequenceDerivedRestriction l E W ⋙
                (coefficientTowerSections l E W).rightDerivedFunctor).obj M) ≫
            (D.systemSectionsEvaluation n).hom.app M =
          (coefficientIntegralSections l E W).map
              ((coefficientSequenceProjection l E W n).app M) ≫
            (D.scalar.scalarSections n).hom.app
              ((coefficientSequenceDerivedEvaluation l E W n).obj M)) := by
  sorry

end WeilConjectures
