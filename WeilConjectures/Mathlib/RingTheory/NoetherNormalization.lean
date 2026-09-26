/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.NoetherNormalization

@[expose] public section

/-!
# Noether normalization in dimension one

Mathlib's `exists_finite_inj_algHom_of_fg` produces a polynomial ring in `s` variables over
which a finitely generated algebra is finite, without identifying `s`. Since an integral
extension preserves the Krull dimension, `s` is the dimension of the algebra; in dimension
one this is a polynomial ring in a single variable.

## Main statements

- `exists_finite_inj_algHom_polynomial_of_ringKrullDim_eq_one`
-/

/-- Blueprint `sk-i-real-normalization`: One-dimensional Noether normalization.

A nonzero finitely generated algebra `B` of Krull dimension one over a field `K` admits an
injective `K`-algebra map from the polynomial ring `K[T]` making `B` a finite module. -/
theorem exists_finite_inj_algHom_polynomial_of_ringKrullDim_eq_one
    (K B : Type*) [Field K] [CommRing B] [Nontrivial B] [Algebra K B]
    [Algebra.FiniteType K B] (hB : ringKrullDim B = 1) :
    ∃ g : Polynomial K →ₐ[K] B, Function.Injective g ∧ g.Finite := by
  sorry
