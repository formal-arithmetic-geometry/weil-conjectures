/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!
# Exactness of restriction to a localized site

## References

* [Stacks Project, Tag 00XZ](https://stacks.math.columbia.edu/tag/00XZ)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- Restriction of abelian sheaves to the localized site is exact. -/
theorem siteRestriction_exact
    {C : Type u} [SmallCategory C]
    (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (W : C)
    (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}))
    (hS : S.ShortExact) :
    (S.map (J.toGrothendieck.overPullback AddCommGrpCat.{u} W)).ShortExact := by
  -- Restriction preserves limits and is also a left adjoint by cover lifting.
  let F := J.toGrothendieck.overPullback AddCommGrpCat.{u} W
  have : Limits.PreservesColimitsOfSize.{u, u} F :=
    ((Over.forget W).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (J.toGrothendieck.over W) J.toGrothendieck).leftAdjoint_preservesColimits
  exact hS.map_of_exact F

end CategoryTheory
