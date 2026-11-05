/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! # Uniqueness of normalized derived adjunctions

Source: Stacks Project, Derived Categories, Tag 09T5.
(blueprint: lem-pc-derived-adjunction-normalization-unique).
-/

@[expose] public section

set_option autoImplicit false

namespace CategoryTheory.Adjunction

variable {C D H J : Type*} [Category* C] [Category* D] [Category* H] [Category* J]
  {T : C ⥤ D} {U : D ⥤ C} {L : H ⥤ J} {R : J ⥤ H}

end CategoryTheory.Adjunction
