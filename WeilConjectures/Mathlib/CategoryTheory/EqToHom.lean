/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.EqToHom

/-! # Morphisms heterogeneously equal to identities -/

@[expose] public section

universe u₁ v₁

namespace CategoryTheory

/-- A morphism heterogeneously equal to an identity is the canonical `eqToHom`. -/
theorem eq_eqToHom_of_heq_id {C : Type u₁} [Category.{v₁} C] {X Y : C} (f : X ⟶ Y)
    (h : X = Y) (hf : HEq f (𝟙 X)) : f = eqToHom h := by
  subst h
  rw [eqToHom_refl]
  exact eq_of_heq hf

end CategoryTheory
