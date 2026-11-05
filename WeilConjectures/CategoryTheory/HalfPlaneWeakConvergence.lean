/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.FinitePageImageQuotient
import WeilConjectures.CategoryTheory.DerivedCoupleExact

/-!
# Canonical quotient maps in half-plane convergence

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2, canonical comparison.
(blueprint: lem-sp-half-plane-weak-convergence)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

end CategoryTheory.BigradedExactCouple
