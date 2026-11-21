/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsCore
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZero

/-! # Normalized coefficient sections and inverse limits

## References

* [Stacks, Tag 03CZ]
* [Stacks, Tag 079P]
* [Stacks, Tag 08JA]
* [Stacks, Tag 0D6E]
* [Stacks, Tag 0941]
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

/-- The resolution-unit equation for sections of the prescribed inverse limit.
This is `CoefficientGlobalLimitModel` with its sole comparison supplied as a parameter. -/
def CoefficientSectionsLimitResolutionEquation
    (κ : coefficientSequenceLimit l E W ⋙ coefficientIntegralSections l E W ≅
      coefficientSequenceDerivedRestriction l E W ⋙
        (coefficientTowerSections l E W).rightDerivedFunctor ⋙
          coefficientMappingLimit.{max u (t + 1)}) : Prop :=
  ∀ (K : CochainComplex (coefficientSequenceModules l E W) ℤ),
    CoefficientComparisonEquation
      (coefficientGlobalLimitLeftComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      ((coefficientIntegralSections l E W).map
          ((coefficientConstantTowerLimit l E W).map
            ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))
      (κ.hom.app (DerivedCategory.Q.obj K))
      (coefficientGlobalLimitRightComparison l E W
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
      (coefficientMappingLimit.{max u (t + 1)}.map
        ((coefficientTowerSections l E W).rightDerivedFunctor.map
          ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.inv.app K)))

attribute [local irreducible] CoefficientSectionsLimitResolutionEquation

/-- Sections comparisons before inserting an internal-Hom fiber. -/
structure CoefficientDerivedSectionsNormalization
    (R : CoefficientDerivedSystemReduction l E W)
    extends CoefficientDerivedSystemScalarCoherence l E W where
  /-- Evaluation of the actual derived tower sections. -/
  systemSectionsEvaluation : ∀ n : ℕ,
    coefficientSequenceDerivedRestriction l E W ⋙
        (coefficientTowerSections l E W).rightDerivedFunctor ⋙
          coefficientMappingEvaluation.{max u (t + 1)} n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteSections l E W n
  /-- The comparison with the specified total inverse limit. -/
  globalLimit : coefficientSequenceLimit l E W ⋙ coefficientIntegralSections l E W ≅
    coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
        coefficientMappingLimit.{max u (t + 1)}
  /-- This comparison extends the ordinary sections/limit comparison. -/
  globalLimit_model : CoefficientSectionsLimitResolutionEquation l E W globalLimit
  /-- Sections of the actual total-limit projection have the specified finite meaning. -/
  sections_projection : ∀ (M : coefficientSequenceDerived l E W) (n : ℕ),
    globalLimit.hom.app M ≫
        (coefficientMappingProjection.{max u (t + 1)} n).app
          ((coefficientSequenceDerivedRestriction l E W ⋙
            (coefficientTowerSections l E W).rightDerivedFunctor).obj M) ≫
        (systemSectionsEvaluation n).hom.app M =
      (coefficientIntegralSections l E W).map
          ((coefficientSequenceProjection l E W n).app M) ≫
        (scalarSections n).hom.app ((coefficientSequenceDerivedEvaluation l E W n).obj M)
  /-- The finite enriched scalar adjunct has the normalized action on H-zero. -/
  scalar_hom_zero : ∀ (n : ℕ)
    (P : DerivedCategory (scalarReductionSource l E W))
    (M : normalizedDVRDerived l E W n)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj
        (op P, (coefficientFiniteDerivedRestriction l E W n).obj M))),
    coefficientFiniteHomEquiv l E W n _ _
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
          ((coefficientIntegralSections l E W).map
              (coefficientEnrichedAdjunctionMap R.integralClosed (R.finiteClosed n)
                (coefficientFiniteDerivedExtension l E W n)
                (coefficientFiniteAdjunction l E W n) (R.finiteTensor n) P M) ≫
            (scalarSections n).hom.app
              ((coefficientFiniteInternalHom l E W n).obj
                (op ((coefficientFiniteDerivedExtension l E W n).obj P), M))) x) =
      ((coefficientFiniteAdjunction l E W n).homEquiv P M).symm
        (coefficientIntegralHomEquiv l E W P _ x)

/-- Sections and total-limit comparisons with their ordinary and H-zero normalizations. -/
theorem coefficientDerivedSectionsNormalization
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R) :
    Nonempty (CoefficientDerivedSectionsNormalization l E W R) := by
  obtain ⟨C⟩ := coefficientDerivedSectionsCore l E W R hF
  refine ⟨{
    toCoefficientDerivedSystemScalarCoherence :=
      C.toCoefficientDerivedSystemScalarCoherence
    systemSectionsEvaluation := C.systemSectionsEvaluation
    globalLimit := C.globalLimit
    globalLimit_model := ?_
    sections_projection := C.sections_projection
    scalar_hom_zero := ?_ }⟩
  · simpa only [CoefficientSectionsLimitResolutionEquation,
      CoefficientSectionsLimitResolutionEquationCore] using C.globalLimit_model
  · exact coefficientDerivedSectionsScalarHomZero l E W R hF
      C.toCoefficientDerivedSystemScalarCoherence

end WeilConjectures
