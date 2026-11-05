/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import all WeilConjectures.CategoryTheory.FinitePageGradedQuotient
import all WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel

/-! # Transport of half-plane abutments along an exact functor -/

@[expose] public section

set_option autoImplicit false
universe u₁ v₁ u₂ v₂
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
section Naturality
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (Φ : C ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
end Naturality

end CategoryTheory.BigradedExactCouple
