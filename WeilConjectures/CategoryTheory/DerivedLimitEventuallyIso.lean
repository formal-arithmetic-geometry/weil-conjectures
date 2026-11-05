/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups

/-!
# Vanishing of the first derived limit of an eventually constant tower

Source: Stacks Project, More on Algebra, Tag 07KW, and Tag 08D4, proof of (2)
(blueprint: lem-pc-derived-limit-eventually-iso).
-/

@[expose] public section

universe u

open CategoryTheory.Limits CategoryTheory.Category

namespace CategoryTheory

attribute [local instance] roosTowerEnoughInjectives roosLimitAdditive

end CategoryTheory
