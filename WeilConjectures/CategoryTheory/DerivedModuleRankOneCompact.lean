/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- The degree-zero explicit free rank-one module is compact in the derived module
category. Source: Stacks Project, Tag 0F5X, first paragraph. -/
theorem derivedModule_rankOne_compact
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))] :
    IsCompactObject
      ((DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S))) := by
  intro I E
  exact ⟨derivedModule_rankOne_comparison_injective (S := S) I E,
    derivedModule_rankOne_comparison_surjective (S := S) I E⟩

end CategoryTheory
