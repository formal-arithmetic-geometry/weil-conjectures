/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

@[expose] public section

universe u v

namespace CategoryTheory

open Limits Opposite
open scoped Simplicial

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

end CategoryTheory
