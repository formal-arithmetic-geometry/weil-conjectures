/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence

/-!
# Normalized colimits of half-plane exact-couple diagonals

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 1, the stable diagonal.
(blueprint: lem-sp-half-plane-diagonal-colimits)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

end CategoryTheory.BigradedExactCouple
