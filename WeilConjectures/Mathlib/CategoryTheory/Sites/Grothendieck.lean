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
covering sieves is covering. We deduce the version for a finite family of covering sieves, in
the form that is most convenient in practice: a sieve containing the intersection of finitely
many covering sieves is covering.
-/

public section

universe v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The infimum of a finite family of covering sieves is covering. -/
lemma finsetInf_mem {X : C} {ι : Type*} (s : Finset ι) (S : ι → Sieve X)
    (hS : ∀ i ∈ s, S i ∈ J X) : s.inf S ∈ J X := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [J.top_mem X]
  | insert a s ha ih =>
    rw [Finset.inf_insert]
    exact J.intersection_covering (hS a (Finset.mem_insert_self a s))
      (ih fun i hi ↦ hS i (Finset.mem_insert_of_mem hi))

lemma finsetInf_apply {X : C} {ι : Type*} (s : Finset ι) (S : ι → Sieve X) {Y : C} (g : Y ⟶ X) :
    (s.inf S) g ↔ ∀ i ∈ s, S i g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Sieve.top_apply]
  | insert a s ha ih => simp [Finset.inf_insert, ih]

/-- A sieve which contains the intersection of a finite family of covering sieves is covering. -/
lemma mem_of_forall_finite {X : C} {ι : Type*} [Finite ι] {T : Sieve X} (S : ι → Sieve X)
    (hS : ∀ i, S i ∈ J X) (hT : ∀ ⦃Y : C⦄ (g : Y ⟶ X), (∀ i, S i g) → T g) : T ∈ J X := by
  classical
  have := Fintype.ofFinite ι
  exact J.superset_covering
    (fun _ g hg ↦ hT g fun i ↦ (finsetInf_apply Finset.univ S g).1 hg i (Finset.mem_univ i))
    (J.finsetInf_mem Finset.univ S fun i _ ↦ hS i)

end CategoryTheory.GrothendieckTopology
