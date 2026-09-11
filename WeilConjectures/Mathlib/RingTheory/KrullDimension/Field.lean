/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# The dimension of a finitely generated domain over a field

The Krull dimension of a domain `A` that is a finitely generated algebra over a field `k` is the
transcendence degree of `A`, equivalently of its field of fractions, over `k`.

The transcendence degree used here is `Algebra.trdeg`, the cardinal-valued transcendence degree of
`Mathlib/RingTheory/AlgebraicIndependent/Basic.lean`: it is defined for an arbitrary algebra, not
just for a field extension, and `Algebra.trdeg k A` therefore already makes sense for the ring `A`
itself. It is finite here, so the comparison with `ringKrullDim A : WithBot ℕ∞` is made through
`Cardinal.toNat`.

## Main results

* `ringKrullDim_eq_trdeg`: `ringKrullDim A = Cardinal.toNat (Algebra.trdeg k A)` for a domain `A`
  which is a finitely generated algebra over a field `k`.
* `ringKrullDim_eq_trdeg_of_isFractionRing`: the same with the transcendence degree taken over the
  field of fractions of `A`, `ringKrullDim A = Cardinal.toNat (Algebra.trdeg k K)`.
* `Algebra.FiniteType.exists_ringKrullDim_le`: a finitely generated algebra over a field has
  finite Krull dimension.
* `ringKrullDim_quotient_lt`: quotienting a finitely generated domain over a field by a nonzero
  prime strictly drops the Krull dimension.

Both are proved from Noether normalization: `A` is finite, hence integral, over a polynomial ring
`k[X₀, …, X_{s-1}]` embedded in it, and both sides of the equality are unchanged on passing to
that subring — the Krull dimension by `Algebra.IsIntegral.ringKrullDim_eq` and the transcendence
degree because `A` is algebraic over it.
-/

@[expose] public section

variable (k : Type*) (A : Type*) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]

/-- **The dimension of a finitely generated domain over a field is its transcendence degree.**

If `A` is a domain which is a finitely generated algebra over a field `k`, then the Krull dimension
of `A` is the transcendence degree of `A` over `k`. -/
theorem ringKrullDim_eq_trdeg : ringKrullDim A = Cardinal.toNat (Algebra.trdeg k A) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) A := IsScalarTower.of_algHom g
  have : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  have hfaithful : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hbase : FaithfulSMul k (MvPolynomial (Fin s) k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (MvPolynomial.C_injective _ _)
  have htrdeg : Cardinal.toNat (Algebra.trdeg k A) = s := by
    have hz : Algebra.trdeg (MvPolynomial (Fin s) k) A = 0 := trdeg_eq_zero
    have h := lift_trdeg_add_eq k (MvPolynomial (Fin s) k) A
    rw [hz, MvPolynomial.trdeg_of_isDomain] at h
    simpa using congrArg Cardinal.toNat h.symm
  rw [htrdeg, Algebra.IsIntegral.ringKrullDim_eq (MvPolynomial (Fin s) k) A,
    MvPolynomial.ringKrullDim_fin_of_field]

/-- **The dimension of a finitely generated domain over a field is the transcendence degree of its
function field.**

If `A` is a domain which is a finitely generated algebra over a field `k` and `K` is a field of
fractions of `A`, then the Krull dimension of `A` is the transcendence degree of `K` over `k`. -/
@[stacks 00P0]
theorem ringKrullDim_eq_trdeg_of_isFractionRing (K : Type*) [Field K] [Algebra A K] [Algebra k K]
    [IsScalarTower k A K] [IsFractionRing A K] :
    ringKrullDim A = Cardinal.toNat (Algebra.trdeg k K) := by
  have : FaithfulSMul k A :=
    (faithfulSMul_iff_algebraMap_injective k A).mpr (algebraMap k A).injective
  have h : Cardinal.toNat (Algebra.trdeg k K) = Cardinal.toNat (Algebra.trdeg k A) := by
    simpa using congrArg Cardinal.toNat (IsFractionRing.lift_trdeg_eq k A K)
  rw [h, ringKrullDim_eq_trdeg k A]

/-- A finitely generated algebra over a field has finite Krull dimension: it is a quotient of a
polynomial ring in finitely many variables. -/
theorem Algebra.FiniteType.exists_ringKrullDim_le (k : Type*) (A : Type*) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : ∃ n : ℕ, ringKrullDim A ≤ n := by
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  refine ⟨n, ?_⟩
  rw [← MvPolynomial.ringKrullDim_fin_of_field k n]
  exact ringKrullDim_le_of_surjective φ.toRingHom hφ

/-- A ring which is of finite type over a field has finite Krull dimension. -/
theorem RingHom.FiniteType.exists_ringKrullDim_le {k A : Type*} [Field k] [CommRing A]
    {φ : k →+* A} (hφ : φ.FiniteType) : ∃ n : ℕ, ringKrullDim A ≤ n :=
  let _ : Algebra k A := φ.toAlgebra
  have : Algebra.FiniteType k A := hφ
  Algebra.FiniteType.exists_ringKrullDim_le k A

include k in
/-- **Quotienting by a nonzero prime lowers the dimension.**

If `A` is a domain which is a finitely generated algebra over a field `k` and `p` is a nonzero
prime ideal of `A`, then `dim (A ⧸ p) < dim A`.

A nonzero element of `p` is a nonzero divisor of `A`, so any chain of primes of `A ⧸ p` extends
by the zero ideal to a chain of primes of `A` of length one more; the dimension of `A ⧸ p` is
finite because `A ⧸ p` is again a finitely generated `k`-algebra. -/
theorem ringKrullDim_quotient_lt (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    ringKrullDim (A ⧸ p) < ringKrullDim A := by
  obtain ⟨r, hrp, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  have hle : ringKrullDim (A ⧸ p) + 1 ≤ ringKrullDim A :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.mpr hrp)
  rw [ringKrullDim_eq_trdeg k (A ⧸ p)] at hle ⊢
  exact ENat.WithBot.add_one_le_iff.mp hle
