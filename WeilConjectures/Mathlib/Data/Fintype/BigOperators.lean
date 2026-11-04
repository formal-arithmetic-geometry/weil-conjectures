/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Data.Fintype.BigOperators

/-!
# Sums over a subtype as dependent-`if` sums

`Fintype.sum_subtype_eq_sum_dite` rewrites a sum over a subtype as a sum over the ambient type of
a dependent `if`.
-/

@[expose] public section

/-- A sum over a subtype equals the sum over the ambient type of the dependent `if`. -/
lemma Fintype.sum_subtype_eq_sum_dite {α M : Type*} [Fintype α] [AddCommMonoid M]
    (P : α → Prop) [DecidablePred P] [Fintype (Subtype P)] (g : Subtype P → M) :
    ∑ q : Subtype P, g q = ∑ q, if h : P q then g ⟨q, h⟩ else 0 := by
  calc ∑ q : Subtype P, g q
      = ∑ q : Subtype P, if h : P q.val then g ⟨q.val, h⟩ else 0 :=
        Fintype.sum_congr _ _ fun q ↦ by rw [dif_pos q.2]
    _ = ∑ x ∈ Finset.univ.filter P, (fun x ↦ if h : P x then g ⟨x, h⟩ else 0) x :=
        (Finset.sum_subtype _ (fun _ ↦ Finset.mem_filter_univ _)
          (fun x ↦ if h : P x then g ⟨x, h⟩ else 0)).symm
    _ = _ := by
        rw [Finset.sum_filter]
        exact Fintype.sum_congr _ _ fun q ↦ by split_ifs <;> rfl
