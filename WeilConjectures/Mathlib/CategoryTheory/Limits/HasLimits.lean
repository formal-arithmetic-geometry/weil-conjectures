/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# Limits and colimits of size `u` from limits and colimits of size `u + 1`

The coefficient categories of this development have `Hom`-types in the universe `u + 1`, one
above the universe `u` of the base schemes, and a Grothendieck abelian such category has
limits and colimits of size `u + 1` by `CategoryTheory.IsGrothendieckAbelian.hasLimits` and
`CategoryTheory.IsGrothendieckAbelian.hasColimits`. The limits and colimits indexed by the
small sites — for instance the colimits computing a stalk, or the products entering the
skyscraper sheaf at a geometric point — are of size `u`, so they have to be obtained by
shrinking. Mathlib's `CategoryTheory.Limits.hasLimitsOfSizeShrink` and
`CategoryTheory.Limits.hasColimitsOfSizeShrink` do exactly this, but are deliberately not
instances: in that generality instance search would climb the universes without terminating.

This file registers the two consequences of them that the development needs, so that
`HasLimitsOfSize.{u, u} A` and `HasColimitsOfSize.{u, u} A` need not be carried as
hypotheses alongside `IsGrothendieckAbelian.{u + 1} A`.

-/

@[expose] public section

universe u' u

namespace CategoryTheory.Limits

/-- A category with `Hom`-types in `u + 1` and limits of size `u + 1` has limits of size
`u`, by `hasLimitsOfSizeShrink`.

Instance search does not climb the universes here: discharging the hypothesis
`HasLimitsOfSize.{u + 1, u + 1} A` through this very instance would require
`Category.{u + 2} A`, which the `Category.{u + 1} A` binder rules out. The priority is `low`
so that this attempt is made only after the instances which do provide limits of size
`u + 1`; tried first it aborts elaboration with a universe constraint error instead of
failing silently. -/
instance (priority := low) hasLimitsOfSize_of_succ (A : Type u') [Category.{u + 1} A]
    [HasLimitsOfSize.{u + 1, u + 1} A] : HasLimitsOfSize.{u, u} A :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} A

/-- A category with `Hom`-types in `u + 1` and colimits of size `u + 1` has colimits of
size `u`, by `hasColimitsOfSizeShrink`.

Instance search does not climb the universes here: discharging the hypothesis
`HasColimitsOfSize.{u + 1, u + 1} A` through this very instance would require
`Category.{u + 2} A`, which the `Category.{u + 1} A` binder rules out. As for
`hasLimitsOfSize_of_succ` the priority is `low`, so that the attempt is made only after the
instances which do provide colimits of size `u + 1`. -/
instance (priority := low) hasColimitsOfSize_of_succ (A : Type u') [Category.{u + 1} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] : HasColimitsOfSize.{u, u} A :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} A

end CategoryTheory.Limits
