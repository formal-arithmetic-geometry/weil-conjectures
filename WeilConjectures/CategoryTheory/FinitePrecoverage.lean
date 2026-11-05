/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.Precoverage

/-! # Finite indexed covering axioms

Source: Stacks Project, Sites, Definition 00VH and Lemma 09YL.
(blueprint: def-weil-pbc-finite-precoverage)
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.Precoverage

variable {C : Type u} [Category.{v} C]

end CategoryTheory.Precoverage
