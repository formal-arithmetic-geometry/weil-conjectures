/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.CategoryTheory.DerivedCoupleExact
import WeilConjectures.CategoryTheory.FiniteCycleDerivedComparison
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Finite exact-couple quotient kernels

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 2;
Stacks Project, Tags 011R, 011T and 0AMJ.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

end CategoryTheory.BigradedExactCouple
