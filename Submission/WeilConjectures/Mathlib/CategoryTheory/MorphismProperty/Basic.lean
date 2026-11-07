/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Functor.OfSequence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Composition

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.MorphismProperty.Composition`).
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty


lemma ofOpSequence_map_of_isMultiplicative {C : Type*} [Category C] {X : ℕ → C}
    (f : (n : ℕ) → X (n + 1) ⟶ X n) {m n : ℕ} (hle : m ≤ n) (P : MorphismProperty C)
    [P.IsMultiplicative] (H : ∀ n, P (f n)) :
    P ((Functor.ofOpSequence f).map (homOfLE hle).op) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => simpa using P.id_mem _
  | succ n ih =>
    rw [← homOfLE_comp (show m ≤ m + n by lia) (show m + n ≤ m + (n + 1) by lia),
      op_comp, Functor.map_comp]
    apply P.comp_mem
    · simp [H]
    · apply ih

end CategoryTheory.MorphismProperty
