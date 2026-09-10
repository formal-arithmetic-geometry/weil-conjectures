/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# The Krull dimension of a polynomial ring over a field

`MvPolynomial.ringKrullDim_fin_of_field`: the polynomial ring in `n` variables over a field
has Krull dimension `n`.

This is not new mathematics: it is `MvPolynomial.ringKrullDim_of_isNoetherianRing`
(`dim R[X₁, …, Xₙ] = dim R + n` for `R` Noetherian) combined with
`ringKrullDim_eq_zero_of_field` (`dim k = 0`). Only the two do not live in a common Mathlib
file, so the combination has nowhere to be stated there.
-/

@[expose] public section

/-- The polynomial ring in `n` variables over a field has Krull dimension `n`. -/
theorem MvPolynomial.ringKrullDim_fin_of_field (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
