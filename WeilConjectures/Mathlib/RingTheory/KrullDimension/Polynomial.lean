/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Krull dimension of finitely generated algebras

## Main results

- `ringKrullDim_ne_top_of_finiteType`: a finitely generated algebra over a field has finite Krull
  dimension.
-/

@[expose] public section

/-- A finitely generated algebra over a field has finite Krull dimension. -/
theorem ringKrullDim_ne_top_of_finiteType (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] : ringKrullDim A ≠ ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType k A›
  refine ne_top_of_le_ne_top ?_ (ringKrullDim_le_of_surjective f.toRingHom hf)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  intro h
  cases h
