/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!

# Limits of size `u` from limits of size `u + 1`

This is the dual of `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize`:
the coefficient categories of this development have `Hom`-types in the universe `u + 1`,
one above the universe `u` of the base schemes, and a Grothendieck abelian such category has
limits of size `u + 1` by `CategoryTheory.IsGrothendieckAbelian.hasLimits`. The limits
indexed by the small sites — for instance the products entering the skyscraper sheaf at a
geometric point — are of size `u`, so they have to be obtained by shrinking. Mathlib's
`CategoryTheory.Limits.hasLimitsOfSizeShrink` does exactly this, but is deliberately not an
instance: in that generality instance search would climb the universes without terminating.

-/

@[expose] public section

universe u' u

namespace CategoryTheory.Limits

/-- A category with `Hom`-types in `u + 1` and limits of size `u + 1` has limits of size
`u`, by `hasLimitsOfSizeShrink`.

Instance search does not climb the universes here: discharging the hypothesis
`HasLimitsOfSize.{u + 1, u + 1} A` through this very instance would require
`Category.{u + 2} A`, which the `Category.{u + 1} A` binder rules out. -/
instance hasLimitsOfSize_of_succ (A : Type u') [Category.{u + 1} A]
    [HasLimitsOfSize.{u + 1, u + 1} A] : HasLimitsOfSize.{u, u} A :=
  hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} A

end CategoryTheory.Limits
