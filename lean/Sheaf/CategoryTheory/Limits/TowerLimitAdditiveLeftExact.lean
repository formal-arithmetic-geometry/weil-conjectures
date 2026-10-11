/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Additivity and left exactness of inverse limits of towers

Source: Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1 setup for the
inverse-limit functor (blueprint: lem-pc-tower-limit-left-exact).
-/

universe u

namespace CategoryTheory

open Limits

/-- The inverse-limit functor on towers of abelian groups is additive and left exact.

The towers are the functor category `ℕᵒᵖ ⥤ AddCommGrpCat`; inverse limit is the
limit functor from this category to `AddCommGrpCat`.

1. Using `def-weil-inverse-system` and `lem-pc-tower-abelian`, for a morphism of towers, its
levelwise kernels form the kernel tower, and compatible tuples in the inverse limit
show that the kernel of the induced map is the inverse limit of those kernels. Thus
inverse limit preserves kernels.
2. Using `def-sp-left-exact-additive`, `def-weil-inverse-system`, and
`lem-pc-tower-abelian`, finite biproducts and the zero tower are computed
levelwise, and compatible tuples in a biproduct are pairs of compatible tuples, so
inverse limit is additive. Together these are the additive left exact property of
Stacks Project, More on Algebra, Tag 07KW, Lemma 15.88.1 setup.
(blueprint: lem-pc-tower-limit-left-exact) -/
theorem towerLimitAdditiveLeftExact :
    (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).Additive ∧
      PreservesFiniteLimits
        (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}) := by
  sorry

end CategoryTheory
