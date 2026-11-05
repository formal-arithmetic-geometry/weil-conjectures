/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Single-object quotient comparisons and shifts

Source: Mathlib single functors and their canonical quotient comparisons.
(blueprint: lem-pc-mapped-single-inverse-shift).
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory C]

end CategoryTheory.Functor
