/-
Copyright (c) 2026 The Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Local rings with nilpotent maximal ideal are zero-dimensional

## Main results

- `Ring.KrullDimLE.of_isNilpotent_maximalIdeal`: a local ring whose maximal ideal is nilpotent
  has Krull dimension at most `0`.
-/

@[expose] public section

open IsLocalRing

/-- A local ring whose maximal ideal is nilpotent is zero-dimensional. -/
lemma Ring.KrullDimLE.of_isNilpotent_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    (h : IsNilpotent (maximalIdeal R)) : Ring.KrullDimLE 0 R := by
  obtain ⟨n, hn⟩ := h
  refine Ring.KrullDimLE.mk₀ fun I hI ↦ ?_
  -- a prime `I` contains a power of the maximal ideal, hence the maximal ideal itself
  have hle : maximalIdeal R ≤ I := Ideal.IsPrime.le_of_pow_le (n := n) (by simp [hn])
  have : I = maximalIdeal R := le_antisymm (le_maximalIdeal hI.ne_top) hle
  exact this ▸ maximalIdeal.isMaximal R
