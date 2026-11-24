/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexRestrictOpen
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomologyEvaluationLocalIsoCore

/-!
# A step in the construction of homology evaluation

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- Evaluation is locally an isomorphism under the finite-free model hypotheses. -/
theorem homologyEvaluation_local_iso_of_cycle (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (hJ : ∀ k : ℤ, k ≠ 0 → IsZero (J.homology k))
    (e : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e) (V : X.Opens) (W : V.toScheme.Opens)
    (hI : CochainComplex.IsKInjective ((moduleOpenOverComplexFunctor X V W).obj J))
    (hT : HasFiniteFreeZeroModel (V.toScheme.ringCatSheaf.over W)
      ((moduleOpenOverComplexFunctor X V W).obj T)) :
    IsIso (((Scheme.Modules.restrictFunctor V.ι).map e).over W) := by
  obtain ⟨E, L, q, p, hq, hp, hzero, hsupp, hfree⟩ := hT
  exact homologyEvaluation_local_iso_of_roof X T J n hJ e he V W hI E L q p hq hp
    hzero hsupp hfree

end CategoryTheory
