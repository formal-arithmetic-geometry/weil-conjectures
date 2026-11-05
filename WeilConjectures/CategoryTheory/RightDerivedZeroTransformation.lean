/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# Naturality of the zeroth derived augmentation in the functor

Source: Stacks Project, Tag 0156, zeroth right derived functor and its augmentation.
(blueprint: lem-weil-pbc-right-derived-zero-transformation)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D]

end CategoryTheory
