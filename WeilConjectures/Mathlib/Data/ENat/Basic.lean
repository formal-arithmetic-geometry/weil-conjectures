/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.ENat.Basic

/-!
# Natural numbers are not `⊤` in `WithBot ℕ∞`

## Main results

* `ENat.WithBot.natCast_ne_top`: a natural number, seen in `WithBot ℕ∞`, is not `⊤`.
-/

@[expose] public section

namespace ENat.WithBot

/-- A natural number, seen in `WithBot ℕ∞`, is not `⊤`. -/
@[simp]
theorem natCast_ne_top (n : ℕ) : (n : WithBot ℕ∞) ≠ ⊤ := by
  rw [Ne, eq_top_iff_forall_ge]
  exact fun h ↦ absurd (h (n + 1)) (not_le.2 (by exact_mod_cast Nat.lt_succ_self n))

end ENat.WithBot
