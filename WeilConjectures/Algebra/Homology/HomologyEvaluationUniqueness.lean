/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.Algebra.Homology.HomologyEvaluationLocalCycleLift
import WeilConjectures.Algebra.Homology.HomologyEvaluationUniquenessExt

/-!
# A step in the construction of homology evaluation

## References

* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- Cycle evaluation determines the morphism uniquely. -/
theorem homologyEvaluation_unique_of_cycle (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e e' : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e)
    (he' : IsHomologyEvaluation X T J n e') : e = e' := by
  apply homologyEvaluation_unique_of_cycle_of_local_lifts X T J n e e' he he'
  exact homologyEvaluation_local_cycle_lift X T J n

end CategoryTheory
