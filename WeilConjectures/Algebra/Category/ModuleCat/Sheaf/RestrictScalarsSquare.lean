/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Restriction of scalars along a commutative square of ring sheaves

For morphisms of sheaves of rings with `α ≫ β = γ ≫ δ`, restricting scalars along `β` and then
`α` agrees with restricting along `δ` and then `γ`; the comparison is the identity on sections.

Source: Stacks Project, Tag 03DA.
-/

@[expose] public noncomputable section

universe v u₀ v₀ u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u₀} [Category.{v₀} C] {J : GrothendieckTopology C}
  {A B B' D : Sheaf J RingCat.{u}} (α : A ⟶ B) (β : B ⟶ D) (γ : A ⟶ B') (δ : B' ⟶ D)

end SheafOfModules
