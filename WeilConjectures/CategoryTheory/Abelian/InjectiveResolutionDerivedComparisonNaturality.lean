/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Abelian.InjectiveResolutionDerivedComparison
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# Naturality of the explicit derived resolution comparison

Source: Stacks Project, Derived Categories, Tags 05TE and 015B.
(blueprint: lem-sc-p1-injective-resolution-derived-comparison-naturality).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
  [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]

end CategoryTheory
