/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence

/-!
# Half-plane convergence of an exact couple

Source: blueprint node thm-sp-half-plane-convergence, order 511; Stacks Project,
Tags 011T and 012F (blueprint: thm-sp-half-plane-convergence).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

end CategoryTheory.BigradedExactCouple
