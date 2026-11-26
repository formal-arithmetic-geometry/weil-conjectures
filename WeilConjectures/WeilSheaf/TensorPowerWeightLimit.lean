/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.Weights
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Removing a fixed additive error from all tensor powers

If the Frobenius weight of every power `α ^ k` is at most `k * a + C` for a fixed additive
error `C`, then the weight of `α` is at most `a`. This is the limiting argument in the proof of
semicontinuity of weights for real sheaves: take roots and let the tensor exponent tend to
infinity.
-/

@[expose] public section
set_option autoImplicit false

open AlgebraicGeometry

private theorem le_of_all_nat_mul_le_add {w a C : ℝ}
    (h : ∀ k : ℕ, 0 < k → (k : ℝ) * w ≤ (k : ℝ) * a + C) : w ≤ a := by
  by_contra! hwa
  have hgap : 0 < w - a := sub_pos.mpr hwa
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (w - a))
  have hn' : C / (w - a) < (n + 1 : ℕ) :=
    hn.trans_le (by exact_mod_cast Nat.le_succ n)
  have hC := (div_lt_iff₀ hgap).mp hn'
  have hbound := h (n + 1) (Nat.succ_pos n)
  nlinarith

/-- If the Frobenius weight of `α ^ k` is at most `k * a + C` for every `k > 0`, then the
Frobenius weight of `α` is at most `a`. -/
theorem weight_le_of_all_pow_weight_le
    {E : Type*} [Field E] (ι : E →+* ℂ) (q : ℕ) (α : E) (a C : ℝ)
    (h : ∀ k : ℕ, 0 < k →
      WeilGroup.frobeniusWeight ι q (α ^ k) ≤ (k : ℝ) * a + C) :
    WeilGroup.frobeniusWeight ι q α ≤ a := by
  apply le_of_all_nat_mul_le_add (C := C)
  intro k hk
  have hpow : WeilGroup.frobeniusWeight ι q (α ^ k) =
      (k : ℝ) * WeilGroup.frobeniusWeight ι q α := by
    simp only [WeilGroup.frobeniusWeight, map_pow, norm_pow, Real.log_pow]
    ring
  rw [← hpow]
  exact h k hk
