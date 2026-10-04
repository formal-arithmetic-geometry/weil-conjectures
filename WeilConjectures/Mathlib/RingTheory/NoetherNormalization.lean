/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Noether normalization with the number of variables the Krull dimension

Mathlib's `exists_finite_inj_algHom_of_fg` produces a polynomial ring in `s` variables over
which a finitely generated algebra is finite, without identifying `s`. Since an integral
extension preserves the Krull dimension, `s` is the dimension of the algebra.

## Main statements

- `ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial`: the number of variables of a Noether
  normalization is the Krull dimension.
- `exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq`
- `exists_finite_inj_algHom_polynomial_of_ringKrullDim_eq_one`
- `ringKrullDim_quotient_lt_of_finiteType`: the dimension drops along a proper closed subset of an
  irreducible affine variety.

## Blueprint

- `sk-i-real-normalization`: Noether normalization.
- `lem-zl-noether-normalization-field`: Mathlib's `exists_finite_inj_algHom_of_fg`.
- `lem-zl-noether-normalization-dimension`: `ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial`.
- `sk-i-geometry`: dimension drop.
-/

@[expose] public section

/-- Blueprint `lem-zl-noether-normalization-dimension`: the number of Noether coordinates is the
Krull dimension.

If `K[T₁, …, T_d] → B` is an injective `K`-algebra map over which `B` is a finite module, then
`dim B = d`: the extension is integral, so `dim B = dim K[T₁, …, T_d] = d`. -/
theorem ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial {K B : Type*} [Field K] [CommRing B]
    [Algebra K B] {d : ℕ} (g : MvPolynomial (Fin d) K →ₐ[K] B) (hg : Function.Injective g)
    (hfin : g.Finite) :
    ringKrullDim B = d := by
  algebraize [g.toRingHom]
  have : Module.Finite (MvPolynomial (Fin d) K) B := hfin
  have : FaithfulSMul (MvPolynomial (Fin d) K) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  rw [ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin d) K) B,
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField
      (Field.toIsField K)]
  simp

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
  have : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    simp [ringKrullDim_eq_bot_of_subsingleton] at hB
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg K B
  obtain rfl : s = n := by
    exact_mod_cast (ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hg hfin).symm.trans hB
  exact ⟨g, hg, hfin⟩

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
  obtain ⟨g, hg, hfin⟩ := exists_finite_inj_algHom_mvPolynomial_of_ringKrullDim_eq K B 1 hB
  let e := MvPolynomial.uniqueAlgEquiv K (Fin 1)
  exact ⟨g.comp e.symm.toAlgHom, hg.comp e.symm.injective,
    RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.symm.surjective)⟩

/-- A proper closed subset of an irreducible affine variety has strictly smaller dimension: for a
finitely generated domain `A` over a field and a nonzero prime `P` of `A`,
`dim (A ⧸ P) < dim A`. (blueprint: `sk-i-geometry`) -/
theorem ringKrullDim_quotient_lt_of_finiteType (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    ringKrullDim (A ⧸ P) < ringKrullDim A :=
  ringKrullDim_quotient_lt_of_irreducibleSpace k A hP
