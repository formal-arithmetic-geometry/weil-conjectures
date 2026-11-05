/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Binary products of additive functors to abelian groups

Source: Stacks Project, Homology Tag 0117, and the componentwise description of
cycles and boundaries for finite products.
(blueprint: lem-weil-pbc-right-derived-binary-product)
-/

@[expose] public section

universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section
variable [Abelian C] [HasInjectiveResolutions C]

end

end CategoryTheory
