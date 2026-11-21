/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.Algebra.Homology.HomologyEvaluationCycleExistence
import WeilConjectures.Algebra.Homology.HomologyEvaluationUniqueness
import WeilConjectures.Algebra.Homology.HomologyEvaluationLocalIso

/-! # Homology evaluation and locally split finite free complexes

## References

* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- The uniquely characterized homology evaluation is perfect wherever the first complex
has a finite free zero-differential model and the second is a K-injective resolution
of a degree-zero module. No closed immersion or Koszul regularity enters this lemma. -/
theorem exists_homologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k)) :
    ∃! e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0),
      IsHomologyEvaluation X T J n e ∧
        ∀ (V : X.Opens) (W : V.toScheme.Opens),
          let Fc := moduleOpenOverComplexFunctor X V W
          CochainComplex.IsKInjective (Fc.obj J) →
          HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W) (Fc.obj T) →
          IsIso (((Scheme.Modules.restrictFunctor V.ι).map e).over W) := by
  obtain ⟨e, he⟩ := exists_homologyEvaluation_cycle X T J n
  refine ⟨e, ⟨he, ?_⟩, ?_⟩
  · intro V W
    dsimp only
    intro hI hT
    exact homologyEvaluation_local_iso_of_cycle X T J n hJ e he V W hI hT
  · intro e' h'
    exact (homologyEvaluation_unique_of_cycle X T J n e e' he h'.1).symm

/-- Homology evaluation, specified uniquely by cycle evaluation and its local calculation. -/
noncomputable def homologyEvaluation (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k)) :
    (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0) :=
  (exists_homologyEvaluation X T J n hJ).exists.choose

/-- The local perfection assertion for the uniquely specified evaluation map. -/
theorem homologyEvaluation_isIso (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
    (V : X.Opens) (W : V.toScheme.Opens)
    (hI : CochainComplex.IsKInjective ((moduleOpenOverComplexFunctor X V W).obj J))
    (hT : HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W)
      ((moduleOpenOverComplexFunctor X V W).obj T)) :
    IsIso (((Scheme.Modules.restrictFunctor V.ι).map
      (homologyEvaluation X T J n hJ)).over W) :=
  (exists_homologyEvaluation X T J n hJ).exists.choose_spec.2 V W hI hT

end CategoryTheory
