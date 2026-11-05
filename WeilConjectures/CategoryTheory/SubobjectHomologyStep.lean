/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits

import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Lifting a homology quotient through an epimorphism

Source: blueprint def-sp-convergence, cycle/boundary recursion; Stacks Section 12.20
(blueprint: lem-sp-subobject-homology-step).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

end CategoryTheory
