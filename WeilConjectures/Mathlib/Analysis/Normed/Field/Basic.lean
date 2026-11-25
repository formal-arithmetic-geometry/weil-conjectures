/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Roots of unity have norm one

In a normed division ring, a root of unity has norm `1`, since the norm is multiplicative.
This generalizes `Complex.norm_eq_one_of_pow_eq_one`.
-/

@[expose] public section

variable {α : Type*} [NormedDivisionRing α]

/-- A root of unity in a normed division ring has norm `1`. -/
theorem norm_eq_one_of_pow_eq_one {ζ : α} {n : ℕ} (h : ζ ^ n = 1) (hn : n ≠ 0) : ‖ζ‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn).mp (by rw [← norm_pow, h, norm_one])
