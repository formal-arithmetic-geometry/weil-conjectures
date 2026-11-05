/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # The canonical inclusion of bottom homology

Source: Stacks Project, Tag 05TC (2).
(blueprint: new-lem-pc-derived-bottom-inclusion).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace DerivedCategory.Plus
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

end DerivedCategory.Plus
