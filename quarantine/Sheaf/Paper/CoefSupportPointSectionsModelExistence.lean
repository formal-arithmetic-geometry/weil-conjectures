/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefSupportPointSectionsData
import Sheaf.Paper.CoefSupportPointSectionsComparisonExistence
import all Sheaf.CategoryTheory.CoefficientSequenceGlobalSections
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # Existence of unit-normalized native point sections

Source: Stacks 0D6E and 0941
(blueprint: lem-coef-support-point-sections-model-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefSupportOpenTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def actualSectionsDerivedPair
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] :
    SheafOfModules.SequenceSectionsDerivedPair F where
  functor := F.rightDerivedFunctor
  unit :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun {_ _} f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  universal := by
    have hd := CategoryTheory.derives F
    apply hd.isRightDerivedFunctor_of_isIso
    intro I
    have := I.property
    change IsIso (F.rightDerivedFunctorUnitQ I.obj)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  computes := by
    intro I hI
    have := hI
    change IsIso (F.rightDerivedFunctorUnitQ I)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance

/-- Point sections on the native quotient sequence site have the prescribed
whole-derived comparison and finite evaluations, normalized by derived units.
Source: Stacks, sites-cohomology.tex, lemma-derived-pushforward-composition
(Tag 0D6E), and Tag 0941; support-open-tensor proof step 4.
(blueprint: lem-coef-support-point-sections-model-existence).

Proof: take the whole-derived scalar comparison and its unit equation from
sectionsComparison_exists. Equip the actual ordinary sections functors with
their total right derived functors and rightDerivedFunctorUnitQ. The K-injective
derivability structure proves the universal property, and rightDerivedFunctorUnitQ_eq
proves computation on K-injectives. Apply coefficientTowerComparison to ordinary
level sections and their termwise tower functor. Its normalized unit identity,
after cancelling the inverse evaluation factor, is sectionsEvaluationUnit.
Its all-arrow identity is exactly sectionsEvaluationTransitions at the arrow
(op m) to (op n). Package these fields. No quotient evaluation is asserted to
preserve K-injectives. No inverse limit is taken. -/
theorem sectionsModel_exists (W : Scheme.{u}) : Nonempty (SectionsModel l E W) := by
  obtain ⟨comparison, hcomparison⟩ := sectionsComparison_exists l E W
  let F := ordinaryLevelSections l E W
  let P := actualSectionsDerivedPair F
  let T := actualSectionsDerivedPair (ordinarySections l E W)
  have enoughT (K : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ℤ) :
      ∃ (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ℤ)
        (a : K ⟶ I), I.IsKInjective ∧ QuasiIso a := by
    obtain ⟨I, hI, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, a, hI, ha⟩
  obtain ⟨β, hβ, htβ⟩ := SheafOfModules.coefficientTowerComparison F P T enoughT
  refine ⟨{ comparison := comparison
            comparison_unit := hcomparison
            evaluation := fun n ↦ β (op n)
            evaluation_unit := ?_
            transitions := ?_ }⟩
  · intro n C
    have he := hβ (op n) C
    apply (cancel_epi
      (((CategoryTheory.evaluation ℕᵒᵖ (ModuleCat.{u+1} (coefTraceRing l E))).obj
        (op n)).mapDerivedCategoryFactors.inv.app
          (((ordinarySections l E W).mapHomologicalComplex (.up ℤ)).obj C))).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    simpa only [actualSectionsDerivedPair, F, P, T, integralSections, levelSections,
      coefTraceEvaluation, ordinarySections, ordinaryLevelSections, coefTraceSections,
      Functor.whiskeringRight_obj_comp, Category.assoc] using he
  · intro C m n h
    exact htβ (op m) (op n) (homOfLE h).op C

end WeilConjectures.CoefSupportOpenTensor
