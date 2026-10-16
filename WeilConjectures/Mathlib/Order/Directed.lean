/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Order.Directed
public import Mathlib.Data.Finset.Sort

/-!
# Selected upper bounds of finite sets in a directed preorder

Let `α` be a preorder, `i₀ : α` a base point and `d : α → α → α` a selection of pairwise upper
bounds, i.e. `a ≤ d a b` and `b ≤ d a b`. For a finite set `F` we define the upper bound
`Finset.directedBound i₀ d F` by inserting the elements of `F` one at a time,
`u(∅) = i₀` and `u(F ∪ {i}) = d (u F) i`. Since `d` need not be commutative or associative,
the insertion order matters; we use the order of `Finset.toList`.

## Main definitions and results

- `List.directedBound`, `Finset.directedBound`: the selected upper bound.
- `Finset.le_directedBound`: every element of `F` lies below `Finset.directedBound i₀ d F`.
- `Finset.isDirectedBound`: the selected upper bound attached to a nonempty directed preorder,
  with `d` and `i₀` chosen by `Classical.choice`; `Finset.le_isDirectedBound`.
-/

@[expose] public section

variable {α : Type*}

namespace List

/-- The upper bound of the elements of a list obtained by successively inserting its elements,
starting from the base point `i₀`, using the selected pairwise upper bounds `d`. -/
def directedBound (i₀ : α) (d : α → α → α) (l : List α) : α :=
  l.foldr (fun i b ↦ d b i) i₀

@[simp]
lemma directedBound_nil (i₀ : α) (d : α → α → α) : directedBound i₀ d [] = i₀ := rfl

@[simp]
lemma directedBound_cons (i₀ : α) (d : α → α → α) (i : α) (l : List α) :
    directedBound i₀ d (i :: l) = d (directedBound i₀ d l) i := rfl

variable [Preorder α] {i₀ : α} {d : α → α → α}

lemma base_le_directedBound (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b) (l : List α) :
    i₀ ≤ directedBound i₀ d l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih => exact ih.trans (hd _ _).1

lemma le_directedBound (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b) {l : List α} {i : α} (hi : i ∈ l) :
    i ≤ directedBound i₀ d l := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · exact (hd _ _).2
    · exact (ih hi).trans (hd _ _).1

end List

namespace Finset

/-- Blueprint `def-nagata-directed-finite-upper-bound`: Selected upper bound of a finite set.

Given a base point `i₀` and selected pairwise upper bounds `d`, the upper bound `u F` of a
finite set `F` is defined by insertion: `u ∅ = i₀` and `u (F ∪ {i}) = d (u F) i`, the elements
of `F` being inserted in the order of `Finset.toList`. -/
noncomputable def directedBound (i₀ : α) (d : α → α → α) (F : Finset α) : α :=
  F.toList.directedBound i₀ d

@[simp]
lemma directedBound_empty (i₀ : α) (d : α → α → α) : directedBound i₀ d ∅ = i₀ := by
  simp [directedBound]

variable [Preorder α] {i₀ : α} {d : α → α → α}

/-- Blueprint `lemma-nagata-directed-finite-upper-bound`: Property of the selected finite upper
bound. Every element of `F` lies below the selected upper bound `u F`. -/
lemma le_directedBound (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b) {F : Finset α} {i : α}
    (hi : i ∈ F) : i ≤ directedBound i₀ d F :=
  List.le_directedBound hd (Finset.mem_toList.mpr hi)

/-- The base point lies below the selected upper bound. -/
lemma base_le_directedBound (hd : ∀ a b, a ≤ d a b ∧ b ≤ d a b) (F : Finset α) :
    i₀ ≤ directedBound i₀ d F :=
  List.base_le_directedBound hd _

/-- The selected upper bound of a finite set in a nonempty directed preorder, where the base
point and the pairwise upper bounds are chosen by `Classical.choice`. This is
`Finset.directedBound` for these choices. -/
noncomputable def isDirectedBound [Nonempty α] [IsDirectedOrder α] (F : Finset α) : α :=
  directedBound (Classical.arbitrary α) (fun a b ↦ (exists_ge_ge a b).choose) F

/-- Every element of `F` lies below `Finset.isDirectedBound F`. -/
lemma le_isDirectedBound [Nonempty α] [IsDirectedOrder α] {F : Finset α} {i : α} (hi : i ∈ F) :
    i ≤ isDirectedBound F :=
  le_directedBound (fun a b ↦ (exists_ge_ge a b).choose_spec) hi

end Finset
