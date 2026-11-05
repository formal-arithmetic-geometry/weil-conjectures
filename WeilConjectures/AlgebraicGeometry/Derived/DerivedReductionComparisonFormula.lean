/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The representative equation for derived reduction comparisons

Source: Stacks Project, Tags 06YS and 06YY
(blueprint: def-weil-pbc-derived-reduction-comparison-formula).

The predicate records the ordinary comparison transported through the two specified
reduction counits and the localization factors of exact pullback. Naming the common
formula lets applications share its categorical data without unfolding concrete module
categories and functors during every conversion.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
