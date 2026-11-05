/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-! # Uniqueness of shift commutations

A commutation of a functor with shifts is determined by its isomorphisms; for the
`ℤ`-shift it is determined by its component at one, and it is determined by
compatibility with a natural isomorphism.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

end CategoryTheory.Functor
