/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-!
# Single-object quotient comparisons and shifts

Source: Mathlib single functors and their canonical quotient comparisons.
(blueprint: lem-pc-single-quotient-inverse-shift).
-/

@[expose] public section

universe uB vB
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [HasDerivedCategory B]

end CategoryTheory.Functor
