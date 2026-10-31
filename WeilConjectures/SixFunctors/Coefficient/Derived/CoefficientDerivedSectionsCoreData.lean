/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import all WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceGlobalSections
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSequenceSectionsLimit
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientRestrictionSectionsAcyclic
import all Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Yoneda
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.CategoryTheory.Generator.Basic
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-! Transported data for the normalized coefficient-sections core.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941.
(blueprint: lem-coef-derived-sections-core-data)
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

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence
  SheafOfModules.monoidalCategory HasDerivedCategory.standard

open SheafOfModules in
private theorem scalarSectionsCoherenceExists :
    Nonempty (CoefficientDerivedSystemScalarCoherence l E W) := by
  classical
  choose s hs using scalarSectionsComparison l E W
  let D : CoefficientDerivedSystemScalarData l E W :=
    { scalarSections := s
      ordinaryScalarSections := fun n ↦ ordinaryRestrictionIso.{t+1, t, u}
        (Scheme.ProEt.topology W) (completedIntegralCommRingProjectionUnrestricted l E W n) }
  refine ⟨{ toCoefficientDerivedSystemScalarData := D
            ordinaryScalarSections_formula := ?_
            scalarSections_model := ?_ }⟩
  · intro n M f V b
    let : EssentiallySmall.{max u (t+1)} W.ProEt := essentiallySmallSelf _
    exact ordinaryRestrictionIso_formula.{t+1, t, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingProjectionUnrestricted l E W n) M f V b
  · intro n I
    exact hs n I

open SheafOfModules in
private theorem totalSectionsLimitExists :
    Nonempty (coefficientConstantTowerLimit l E W ⋙ coefficientIntegralSections l E W ≅
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
        coefficientMappingLimit.{max u (t+1)}) := by
  let A := scalarReductionSource l E W
  let F := coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let : IsGrothendieckAbelian.{max u (t+1)} A :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).1
  let : PreservesLimits F := CategoryTheory.preservesLimits_preadditiveCoyoneda_obj _
  let : PreservesLimitsOfSize.{0, 0} F := preservesLimitsOfSize_shrink F
  exact sectionsLimitComparison F

/-- The scalar, finite-evaluation and total-limit data before their two equations.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941; transport through the coefficient
sequence equivalence.
Proof: choose normalized derived sections for the completed coefficient ring and its
quotient tower, transport their scalar and evaluation comparisons through the exact
sequence-site restriction, and transport the ordinary and derived limit comparisons
through the same equivalence. The resulting three fields have exactly the displayed
endpoints.
(blueprint: lem-coef-derived-sections-core-data) -/
structure CoefficientDerivedSectionsCoreData
    (R : CoefficientDerivedSystemReduction l E W) where
  scalar : CoefficientDerivedSystemScalarCoherence l E W
  systemSectionsEvaluation : ∀ n : ℕ,
    coefficientSequenceDerivedRestriction l E W ⋙
        (coefficientTowerSections l E W).rightDerivedFunctor ⋙
          coefficientMappingEvaluation.{max u (t + 1)} n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙ coefficientFiniteSections l E W n
  globalLimit : coefficientSequenceLimit l E W ⋙ coefficientIntegralSections l E W ≅
    coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
        coefficientMappingLimit.{max u (t + 1)}

open SheafOfModules in
/-- The transported scalar/evaluation/limit data exist under finite tensor normalization.
Source: Stacks 03CZ, 079P, 08JA, 0D6E and 0941; extracted construction step of the
normalized coefficient-sections package.
(blueprint: lem-coef-derived-sections-core-data) -/
theorem coefficientDerivedSectionsCoreData
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R) :
    Nonempty (CoefficientDerivedSectionsCoreData l E W R) := by
  have _ := hF
  let : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionSource l E W) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1, t, u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  obtain ⟨D⟩ := scalarSectionsCoherenceExists l E W
  let F := coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
  let P := standardSectionsPair F
  let T := standardSectionsPair (coefficientTowerSections l E W)
  have enough (K : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) :
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (a : K ⟶ I),
        I.IsKInjective ∧ QuasiIso a := by
    obtain ⟨I, hI, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, a, hI, ha⟩
  obtain ⟨β, _⟩ := SheafOfModules.coefficientTowerComparison F P T enough
  obtain ⟨κ⟩ := totalSectionsLimitExists l E W
  refine ⟨{ scalar := D
            systemSectionsEvaluation := fun n ↦ ?_
            globalLimit := Functor.isoWhiskerLeft
              (coefficientSequenceDerivedRestriction l E W) κ }⟩
  exact Functor.isoWhiskerLeft (coefficientSequenceDerivedRestriction l E W) (β (op n)) ≪≫
    Functor.isoWhiskerRight (coefficientRestrictedEvaluationIso l E W n)
      (coefficientIntegralSections l E W) ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E W n) (D.scalarSections n)

end WeilConjectures
