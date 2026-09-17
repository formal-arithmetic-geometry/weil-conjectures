/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.ENat.Basic

/-!
# Natural numbers in `WithBot ℕ∞`

`WithBot ℕ∞` is where the dimension of a sheaf of modules lives, the bottom element being the
dimension `-1` of the empty support, and an induction on that dimension compares it with natural
numbers. This file records the comparisons such an induction needs.

## Main results

* `ENat.WithBot.natCast_ne_top`: a natural number, seen in `WithBot ℕ∞`, is not `⊤`.
* `ENat.WithBot.lt_natCast_zero_iff`: only `⊥` lies below `0`.
* `ENat.WithBot.lt_natCast_add_one_iff`: lying strictly below `n + 1` is lying below or at `n`.
* `ENat.WithBot.lt_natCast_of_add_one_le_natCast`: if `a + 1 ≤ n` then `a < n`.
-/

@[expose] public section

namespace ENat.WithBot

/-- A natural number, seen in `WithBot ℕ∞`, is not `⊤`. -/
@[simp]
theorem natCast_ne_top (n : ℕ) : (n : WithBot ℕ∞) ≠ ⊤ := by
  rw [Ne, eq_top_iff_forall_ge]
  exact fun h ↦ absurd (h (n + 1)) (not_le.2 (by exact_mod_cast Nat.lt_succ_self n))

/-- Only `⊥` lies below `0` in `WithBot ℕ∞`. -/
theorem lt_natCast_zero_iff {a : WithBot ℕ∞} : a < ((0 : ℕ) : WithBot ℕ∞) ↔ a = ⊥ := by
  simpa using _root_.WithBot.lt_coe_bot (α := ℕ∞) (x := a)

/-- In `WithBot ℕ∞`, lying strictly below `n + 1` is lying below or at `n`. -/
theorem lt_natCast_add_one_iff {a : WithBot ℕ∞} {n : ℕ} :
    a < ((n + 1 : ℕ) : WithBot ℕ∞) ↔ a ≤ (n : WithBot ℕ∞) := by
  induction a using _root_.WithBot.recBotCoe with
  | bot => simp
  | coe b =>
    induction b using ENat.recTopCoe with
    | top => simp
    | coe c =>
      exact ⟨fun h ↦ _root_.WithBot.coe_le_coe.2
          (Nat.cast_le.2 (Nat.lt_succ_iff.1 (Nat.cast_lt.1 (_root_.WithBot.coe_lt_coe.1 h)))),
        fun h ↦ _root_.WithBot.coe_lt_coe.2
          (Nat.cast_lt.2 (Nat.lt_succ_of_le (Nat.cast_le.1 (_root_.WithBot.coe_le_coe.1 h))))⟩

/-- In `WithBot ℕ∞`, a bound `a + 1 ≤ n` by a natural number is a strict bound `a < n`. Note
that `⊥ + 1 = ⊥`, so this is genuinely weaker than `a + 1 ≤ b → a < b`, which is false. -/
theorem lt_natCast_of_add_one_le_natCast {a : WithBot ℕ∞} {n : ℕ}
    (h : a + 1 ≤ (n : WithBot ℕ∞)) : a < (n : WithBot ℕ∞) := by
  induction a using _root_.WithBot.recBotCoe with
  | bot => exact bot_lt_iff_ne_bot.2 (by simp)
  | coe b =>
    induction b using ENat.recTopCoe with
    | top =>
      rw [show ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ⊤ from rfl, top_le_iff] at h
      exact absurd h (natCast_ne_top n)
    | coe c =>
      have h' : ((c + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
        push_cast
        exact _root_.WithBot.coe_le_coe.1 h
      exact _root_.WithBot.coe_lt_coe.2 (Nat.cast_lt.2 (Nat.cast_le.1 h'))

end ENat.WithBot
