/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonEvaluationIsIso

/-! # Invertibility of the restricted derived-Hom evaluation map

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- Evaluation at the represented identity induces an isomorphism in every degree. -/
theorem isIso_rawRestrictedCohomologyComparison {S Y : Scheme.{v}} (h : Y ⟶ S)
    (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (U : S.Etale) :
    IsIso (rawRestrictedCohomologyComparison h p F U) := by
  let W := (MorphismProperty.Over.pullback @Etale ⊤ h).obj U
  let A := (upperStar AddCommGrpCat.{v + 1} h).obj
    (RawRestrictedComparison.freeSheaf S U)
  let x := (RawRestrictedComparison.zeroIso W A).inv
    (RawRestrictedComparison.generator h U)
  let T := RawRestrictedComparison.sectionsFunctor W ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
  have he : IsIso (RawRestrictedComparison.Evaluation.evaluate T x) :=
    isIso_rawRestrictedCohomologyComparisonEvaluation h p F U
  dsimp [rawRestrictedCohomologyComparison, W, A, x, T]
  infer_instance

end AlgebraicGeometry.Etale
