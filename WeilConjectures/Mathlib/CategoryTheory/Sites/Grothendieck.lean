/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite intersections of covering sieves

`CategoryTheory.GrothendieckTopology.intersection_covering` says that the intersection of two
covering sieves is covering. We deduce the version for a finite family of covering sieves.
-/

@[expose] public section

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The infimum of a finite family of covering sieves is covering. -/
lemma iInf_mem {X : C} {ι : Type*} [Finite ι] (S : ι → Sieve X) (hS : ∀ i, S i ∈ J X) :
    ⨅ i, S i ∈ J X := by
  have := Fintype.ofFinite ι
  rw [show ⨅ i, S i = Finset.univ.inf S by simp [Finset.inf_eq_iInf]]
  exact Finset.inf_induction (J.top_mem X) (fun _ h₁ _ h₂ ↦ J.intersection_covering h₁ h₂)
    fun i _ ↦ hS i

end CategoryTheory.GrothendieckTopology
