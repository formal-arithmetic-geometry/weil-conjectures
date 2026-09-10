/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

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
