/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Auxiliary results for Abhyankar's lemma

* `AdjoinRoot.formallyUnramified_X_pow_sub_C`: `R[X]/(Xᵉ - u)` is formally unramified over `R`
  when `e` and `u` are invertible in `R`.
* `AlgHom.range_eq_integralClosure_of_isReduced`: a criterion identifying the integral closure
  of `R` in an `R`-algebra `A` with the image of an `R`-algebra `D`, when `D ⧸ tD` is reduced.
-/

@[expose] public section

open Polynomial

/-- `R[X]/(f)` is formally unramified over `R` when `f'` is invertible at the root. -/
theorem AdjoinRoot.formallyUnramified_of_isUnit_aeval_derivative {R : Type*} [CommRing R]
    {f : R[X]} (hf : IsUnit (aeval (AdjoinRoot.root f) (derivative f))) :
    Algebra.FormallyUnramified R (AdjoinRoot f) := by
  constructor
  have hD : KaehlerDifferential.D R (AdjoinRoot f) (AdjoinRoot.root f) = 0 := by
    have h0 := (KaehlerDifferential.D R (AdjoinRoot f)).map_aeval f (AdjoinRoot.root f)
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero] at h0
    exact (hf.smul_eq_zero).mp h0.symm
  refine subsingleton_of_forall_eq 0 fun ω ↦ ?_
  have hω : ω ∈ Submodule.span (AdjoinRoot f)
      (Set.range (KaehlerDifferential.D R (AdjoinRoot f))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | zero => rfl
  | mem x hx =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [← AdjoinRoot.aeval_eq, Derivation.map_aeval, hD, smul_zero]
  | add x y _ _ hx hy => rw [hx, hy, add_zero]
  | smul a x _ hx => rw [hx, smul_zero]

/-- `R[X]/(Xᵉ - u)` is formally unramified over `R` when `e` and `u` are invertible. -/
theorem AdjoinRoot.formallyUnramified_X_pow_sub_C {R : Type*} [CommRing R] {e : ℕ} {u : R}
    (he : IsUnit (e : R)) (hu : IsUnit u) :
    Algebra.FormallyUnramified R (AdjoinRoot (X ^ e - C u)) := by
  refine AdjoinRoot.formallyUnramified_of_isUnit_aeval_derivative ?_
  have hr : AdjoinRoot.root (X ^ e - C u) ^ e = algebraMap R _ u := by
    have h0 := AdjoinRoot.mk_self (f := X ^ e - C u)
    rw [← AdjoinRoot.aeval_eq, map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h0
    exact h0
  rcases e with _ | e
  · simp only [Nat.cast_zero, isUnit_zero_iff] at he
    have : Subsingleton (AdjoinRoot (X ^ 0 - C u)) := by
      rw [← subsingleton_iff_zero_eq_one,
        ← map_zero (algebraMap R (AdjoinRoot (X ^ 0 - C u))), he, map_one]
    exact isUnit_of_subsingleton _
  have hroot : IsUnit (AdjoinRoot.root (X ^ (e + 1) - C u)) := by
    rw [← isUnit_pow_iff e.succ_ne_zero, hr]
    exact hu.map _
  simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul, map_natCast,
    map_pow, aeval_X]
  rw [← map_natCast (algebraMap R (AdjoinRoot (X ^ (e + 1) - C u)))]
  exact (he.map _).mul (hroot.pow _)

/-- Reduction of a monic polynomial `p` after scaling its roots by `s`: all coefficients except
the leading one are divisible by `s`. -/
theorem aeval_scaleRoots_eq_pow_of_monic {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : R[X]} (hp : p.Monic) {s : R} (hs : algebraMap R S s = 0) (x : S) :
    aeval x (p.scaleRoots s) = x ^ p.natDegree := by
  rw [aeval_eq_sum_range, natDegree_scaleRoots, Finset.sum_range_succ, coeff_scaleRoots,
    Nat.sub_self, pow_zero, mul_one, hp.coeff_natDegree, one_smul, add_eq_right]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [coeff_scaleRoots, Algebra.smul_def, map_mul, map_pow, hs,
    zero_pow (Nat.sub_ne_zero_of_lt hi), mul_zero, zero_mul]

/-- Let `φ : D → A` be an injective homomorphism of `R`-algebras with `D` integral over `R`, and
`t ∈ R` mapping to a unit of `A` such that every element of `A` lands in `φ(D)` after
multiplication by a power of `t`. If `D ⧸ tD` is reduced, then `φ(D)` is the integral closure of
`R` in `A`. -/
theorem AlgHom.range_eq_integralClosure_of_isReduced {R D A : Type*} [CommRing R] [CommRing D]
    [CommRing A] [Algebra R D] [Algebra R A] [Algebra.IsIntegral R D] (φ : D →ₐ[R] A)
    (hφ : Function.Injective φ) (t : R) (ht : IsUnit (algebraMap R A t))
    (hspan : ∀ a : A, ∃ k : ℕ, t ^ k • a ∈ φ.range)
    [IsReduced (D ⧸ Ideal.span {algebraMap R D t})] :
    φ.range = integralClosure R A := by
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨d, rfl⟩
    exact (Algebra.IsIntegral.isIntegral d).map φ
  obtain ⟨k, hk⟩ := hspan x
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    obtain ⟨d, hd⟩ := hk
    obtain ⟨p, hp, hpx⟩ := hx
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hd
    have hq : aeval d (p.scaleRoots (t ^ (k + 1))) = 0 := by
      apply hφ
      rw [map_zero, ← Polynomial.aeval_algHom_apply, hd, Algebra.smul_def,
        scaleRoots_aeval_eq_zero (by rwa [aeval_def])]
    let I := Ideal.span {algebraMap R D t}
    have hnil : IsNilpotent (Ideal.Quotient.mk I d) := by
      refine ⟨p.natDegree, ?_⟩
      have hs : algebraMap R (D ⧸ I) (t ^ (k + 1)) = 0 := by
        rw [IsScalarTower.algebraMap_apply R D, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem, map_pow]
        exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ k.succ_pos
      rw [← aeval_scaleRoots_eq_pow_of_monic hp hs, ← Ideal.Quotient.mkₐ_eq_mk R,
        Polynomial.aeval_algHom_apply, hq, map_zero]
    have hdI := hnil.eq_zero
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hdI
    obtain ⟨d₁, rfl⟩ := hdI
    refine ih ⟨d₁, ht.mul_left_cancel ?_⟩
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Algebra.smul_def, ← Algebra.smul_def, smul_smul, ← pow_succ', ← hd, map_mul,
      AlgHom.commutes, mul_comm, Algebra.smul_def]
