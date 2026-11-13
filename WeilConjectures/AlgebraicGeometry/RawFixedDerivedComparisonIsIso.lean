/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawFixedDerivedComparison

/-! # Invertibility of fixed-coefficient raw evaluation

## References

* [Stacks Project, Tag 03Q8](https://stacks.math.columbia.edu/tag/03Q8)
* [Stacks Project, Tag 0GIT](https://stacks.math.columbia.edu/tag/0GIT)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Fixed-coefficient raw evaluation is invertible, including empty charts. -/
theorem isIso_rawFixedDerivedComparison {B T Y : Scheme.{u}}
    (h : Y ⟶ B) (g : Y ⟶ T)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) (U : B.Etale) : IsIso (rawFixedDerivedComparison h g K q U) := by
  have := isIso_rawRestrictedDerivedComparison h q
    ((D+((g)^*[AddCommGrpCat.{u + 1}])).obj K) U
  unfold rawFixedDerivedComparison
  infer_instance


end AlgebraicGeometry.Etale
