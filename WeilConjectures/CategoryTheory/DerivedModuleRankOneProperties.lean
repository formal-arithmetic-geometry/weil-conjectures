/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- The degree-zero complex on the explicit free rank-one left module is a compact
weak generator. Source: Stacks Project, Tag 0F5X, first paragraph, and Tag 07D9,
clauses (1)-(2). -/
theorem derivedModule_rankOne_properties
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))] :
    let P := (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
      (ModuleCat.of S (ULift.{vH} S))
    IsCompactObject P ∧ IsWeakTriangulatedGenerator P := by
  dsimp
  exact ⟨derivedModule_rankOne_compact (S := S),
    derivedModule_rankOne_generator (S := S)⟩

end CategoryTheory
