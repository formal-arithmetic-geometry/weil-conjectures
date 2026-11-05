/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! # A component API for the clopen comparison composite

Source: the functorial composite in Stacks Tag 0F7B, first proof paragraph
(blueprint: def-cbc-clopen-mate-composite).
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory

variable {A B C D E : Type*} [Category* A] [Category* B] [Category* C]
  [Category* D] [Category* E]

end CategoryTheory
