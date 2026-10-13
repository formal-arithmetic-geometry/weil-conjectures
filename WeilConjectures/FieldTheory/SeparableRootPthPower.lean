/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

import Mathlib.FieldTheory.KummerPolynomial

/-!
# Roots of polynomials with p-th-power coefficients

Source: Stacks Project, Fields, Lemma Tag 031V, part (2)
(blueprint: lem-weil-pbc-separable-root-pth-power).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Polynomial

/-- A root in a separable algebraic extension of a nonzero polynomial with distinct roots
and p-th-power coefficients is itself a p-th power.
Source: Stacks Project, Fields, Tag 031V (2)
(blueprint: lem-weil-pbc-separable-root-pth-power).

Proof:
1. The absence of repeated roots makes P coprime to its derivative: a nonconstant common
   divisor would have a root in AlgebraicClosure E and give a repeated root of P.
2. A Bezout identity transports this absence of repeated roots to an algebraic closure
   of L (def-weil-algebraic-closure, def-pc-separable-polynomial).
3. Choose p-th roots of the coefficients to form Q. Coefficientwise Frobenius maps Q to P
   and satisfies Q(gamma)^p = P(gamma^p) (def-weil-ring-frobenius).
4. A repeated root of Q would, under Frobenius, give a repeated root of P.
5. In the closure of L choose gamma with gamma^p = alpha. Then Q(gamma) = 0 and
   X^p - alpha = (X - gamma)^p.
6. If alpha were not a p-th power in L, lem-weil-pbc-x-pow-p-minus-t-irreducible makes
   X^p - alpha irreducible. Its common root with Q forces it to divide Q, giving a
   repeated root since p is at least two, a contradiction. -/
theorem exists_pow_eq_of_distinct_roots_coeff_pow
    {E : Type u} {L : Type v} [Field E] [Field L] [Algebra E L]
    (p : ℕ) [Fact p.Prime] [CharP E p] [Algebra.IsSeparable E L]
    (α : L) (P : E[X]) (hroot : aeval α P = 0) (hne : P ≠ 0)
    (hdistinct : ∀ ρ : AlgebraicClosure E,
      ¬ (X - C ρ) ^ 2 ∣ P.map (algebraMap E (AlgebraicClosure E)))
    (hcoeff : ∀ n : ℕ, ∃ b : E, P.coeff n = b ^ p) :
    ∃ α' : L, α = α' ^ p := by
  classical
  have hmapne : P.map (algebraMap E (AlgebraicClosure E)) ≠ 0 := map_ne_zero hne
  have hsep : P.Separable := by
    apply (separable_map (algebraMap E (AlgebraicClosure E))).mp
    apply (nodup_roots_iff_of_splits hmapne (IsAlgClosed.splits _)).mp
    rw [Multiset.nodup_iff_count_le_one]
    intro ρ
    rw [count_roots]
    by_contra h
    exact hdistinct ρ ((le_rootMultiplicity_iff hmapne).mp (by omega))
  have : CharP L p := charP_of_injective_algebraMap (algebraMap E L).injective p
  have hcoeffL : ∀ n, (P.map (algebraMap E L)).coeff n ∈ (frobenius L p).range := by
    intro n
    obtain ⟨b, hb⟩ := hcoeff n
    exact ⟨algebraMap E L b, by simp [coeff_map, hb, frobenius_def]⟩
  obtain ⟨Q, hQ⟩ := (mem_map_range (frobenius L p)).mpr hcoeffL
  change Q.map (frobenius L p) = P.map (algebraMap E L) at hQ
  have hQsep : Q.Separable :=
    (separable_map (frobenius L p)).mp (hQ.symm ▸ hsep.map)
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap L (AlgebraicClosure L) α) (Fact.out : p.Prime).pos
  have hQroot : aeval γ Q = 0 := by
    have heval : (aeval γ Q) ^ p = 0 := by
      change frobenius (AlgebraicClosure L) p
        (Q.eval₂ (algebraMap L (AlgebraicClosure L)) γ) = 0
      rw [hom_eval₂, ← RingHom.frobenius_comm, ← eval₂_map, hQ]
      change (P.map (algebraMap E L)).eval₂
        (algebraMap L (AlgebraicClosure L)) (γ ^ p) = 0
      rw [hγ, eval₂_at_apply]
      have hrootL : (P.map (algebraMap E L)).eval α = 0 := by
        simpa only [eval_map, ← aeval_def] using hroot
      rw [hrootL, map_zero]
    exact eq_zero_of_pow_eq_zero heval
  have hγsep : IsSeparable L γ :=
    hQsep.of_dvd (minpoly.dvd L γ hQroot)
  by_contra hpow
  have hirr : Irreducible (X ^ p - C α) :=
    X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) (by
      intro β hβ
      exact hpow ⟨β, hβ.symm⟩)
  have hmin : minpoly L γ = X ^ p - C α :=
    (minpoly.eq_of_irreducible_of_monic (x := γ) hirr (by simp [hγ])
      (monic_X_pow_sub_C α (Fact.out : p.Prime).ne_zero)).symm
  have hunit : IsUnit (X ^ p - C α) := by
    simpa [IsSeparable, hmin, separable_def, derivative_X_pow, CharP.cast_eq_zero,
      isCoprime_zero_right]
      using hγsep
  exact hirr.not_isUnit hunit

end Polynomial
