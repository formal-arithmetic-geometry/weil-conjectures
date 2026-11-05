/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Comparing boundaries after extension by zero

Source: Stacks Project, Homology, Tag 0117; Derived Categories, Tag 014Q.
(blueprint: lem-sc-p1-nat-complex-derived-boundary).
-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

end CategoryTheory
