/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Noether normalization with the number of variables the Krull dimension

Mathlib's `exists_finite_inj_algHom_of_fg` produces a polynomial ring in `s` variables over
which a finitely generated algebra is finite, without identifying `s`. Since an integral
extension preserves the Krull dimension, `s` is the dimension of the algebra.

## Main statements

- `exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq`
- `exists_finite_inj_algHom_polynomial_of_ringKrullDim_eq_one`
- `ringKrullDim_quotient_lt_of_finiteType`: the dimension drops along a proper closed subset of an
  irreducible affine variety.

## Blueprint

- `sk-i-real-normalization`: Noether normalization.
- `sk-i-geometry`: dimension drop.
-/

@[expose] public section

/-- Noether normalization in the sharp form: a finitely generated algebra `B` of Krull
dimension `n` over a field `K` admits an injective `K`-algebra map from the polynomial ring in
`n` variables making `B` a finite module.

The number of variables is forced: a finite injective algebra map is an integral extension,
and an integral extension preserves the Krull dimension, so the polynomial ring produced by
`exists_finite_inj_algHom_of_fg` has `ringKrullDim B` many variables. -/
theorem exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq
    (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Algebra.FiniteType K B] (n : ℕ)
    (hB : ringKrullDim B = (n : ℕ)) :
    ∃ g : MvPolynomial (Fin n) K →ₐ[K] B, Function.Injective g ∧ g.Finite := by
  sorry

/-- Blueprint `sk-i-real-normalization`: One-dimensional Noether normalization.

A finitely generated algebra `B` of Krull dimension one over a field `K` admits an injective
`K`-algebra map from the polynomial ring `K[T]` making `B` a finite module.

Nontriviality of `B` is automatic: the zero ring has `ringKrullDim = ⊥`. This is the case
`n = 1` of `exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq`, along the isomorphism
`MvPolynomial (Fin 1) K ≃ₐ[K] K[T]`. -/
theorem exists_finite_inj_algHom_polynomial_of_ringKrullDim_eq_one
    (K B : Type*) [Field K] [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (hB : ringKrullDim B = 1) :
    ∃ g : Polynomial K →ₐ[K] B, Function.Injective g ∧ g.Finite := by
  sorry

/-- A proper closed subset of an irreducible affine variety has strictly smaller dimension: for a
finitely generated domain `A` over a field and a nonzero prime `P` of `A`,
`dim (A ⧸ P) < dim A`. (blueprint: `sk-i-geometry`) -/
theorem ringKrullDim_quotient_lt_of_finiteType (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    ringKrullDim (A ⧸ P) < ringKrullDim A :=
  ringKrullDim_quotient_lt_of_irreducibleSpace k A hP
