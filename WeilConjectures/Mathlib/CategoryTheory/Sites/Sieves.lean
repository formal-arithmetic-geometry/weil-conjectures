/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Sieves

/-!
# Membership in an infimum of sieves

`CategoryTheory.Sieve.sInf_apply` describes membership in the infimum of a set of sieves.
We record the corresponding statement for an indexed family.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Sieve

variable {C : Type u} [Category.{v} C] {X : C}

/-- A morphism belongs to the infimum of a family of sieves iff it belongs to each of them. -/
@[simp]
theorem iInf_apply {ι : Sort*} {S : ι → Sieve X} {Y : C} (g : Y ⟶ X) :
    (⨅ i, S i) g ↔ ∀ i, S i g := by
  simp [iInf]

end CategoryTheory.Sieve
