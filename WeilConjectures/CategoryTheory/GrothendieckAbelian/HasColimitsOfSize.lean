/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# (Co)limits of size `u` from (co)limits of size `u + 1`

The coefficient categories of this development have `Hom`-types in the universe `u + 1`,
one above the universe `u` of the base schemes, and a Grothendieck abelian such category
has colimits and limits of size `u + 1` by
`CategoryTheory.IsGrothendieckAbelian.hasColimits` and
`CategoryTheory.IsGrothendieckAbelian.hasLimits`. The (co)limits indexed by the small
sites are of size `u`, so they have to be obtained by shrinking. Mathlib's
`CategoryTheory.Limits.hasColimitsOfSizeShrink` and
`CategoryTheory.Limits.hasLimitsOfSizeShrink` do exactly this, but are deliberately not
instances: in that generality instance search would climb the universes without
terminating.

This file registers the consequences of them that the development needs, so that
`HasColimitsOfSize.{u, u} A` and `HasLimitsOfSize.{u, u} A` — the latter in particular
supplying the `HasProducts.{u} A` that the monoidal structure on étale sheaves asks for —
need not be carried as hypotheses alongside `IsGrothendieckAbelian.{u + 1} A`.

-/

@[expose] public section

universe u' u

namespace CategoryTheory.Limits

/-- A category with `Hom`-types in `u + 1` and colimits of size `u + 1` has colimits of
size `u`, by `hasColimitsOfSizeShrink`.

Instance search does not climb the universes here: discharging the hypothesis
`HasColimitsOfSize.{u + 1, u + 1} A` through this very instance would require
`Category.{u + 2} A`, which the `Category.{u + 1} A` binder rules out. -/
instance hasColimitsOfSize_of_succ (A : Type u') [Category.{u + 1} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] : HasColimitsOfSize.{u, u} A :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A

/-- A category with `Hom`-types in `u + 1` and limits of size `u + 1` has limits of size
`u`, by `hasLimitsOfSizeShrink`. It is loop-free for the same reason as
`hasColimitsOfSize_of_succ`. -/
instance hasLimitsOfSize_of_succ (A : Type u') [Category.{u + 1} A]
    [HasLimitsOfSize.{u + 1, u + 1} A] : HasLimitsOfSize.{u, u} A :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} A

end CategoryTheory.Limits
