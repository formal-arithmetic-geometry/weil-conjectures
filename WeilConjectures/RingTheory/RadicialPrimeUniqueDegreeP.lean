/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Powers and unique primes in a degree-p root extension

Source: Stacks Project, More on Algebra, Tag 07PR, proof; Algebra, Tags 0BR8 and 00GQ
(blueprint: lem-weil-pbc-radicial-prime-unique-degree-p).
-/

@[expose] public section

universe u

open Polynomial

namespace AdjoinRoot

/-- Source: Stacks Project, More on Algebra, Tag 07PR, proof, and Algebra, Tags 0BR8 and
00GQ (blueprint: lem-weil-pbc-radicial-prime-unique-degree-p).
For domains `R` and `R[X]/(X^p-f)` with prime `p` zero in `R`, the structure map is
injective and integral, every p-th power comes from `R`, and every prime of `R` has a
unique prime above it.

Proof:
1. The polynomial `X^p-C f` is monic of degree `p`. The quotient is free with basis
   `1, z, ..., z^(p-1)` (lem-weil-pbc-monic-quotient-free). Comparing the coefficient of
   `1` proves injectivity. This finite free algebra is integral
   (lem-weil-pbc-finite-algebra-is-integral; def-weil-pbc-integral-closure).
2. The image of `p` in the quotient is zero. In the binomial expansion of `(x+y)^p`,
   every intermediate binomial coefficient is divisible by the prime `p`, so Frobenius
   is additive; induction gives the same identity for finite sums. It is multiplicative
   because the quotient is commutative.
3. Represent an element as a polynomial sum `sum b_i*z^i` (def-weil-polynomial-ring).
   Raising to `p` and using `z^p=f` gives the image of `sum b_i^p*f^i` in `R`.
4. If primes `q` and `q'` contract to `P` and `c` belongs to `q`, write `c^p` as the
   image of `r` in `R`. Then `r` belongs to `P`, so `c^p` belongs to `q'`, and primality
   with `p>0` puts `c` in `q'`. Symmetry gives equality (Tag 0BR8).
5. Injectivity and integrality give existence by lying over
   (lem-weil-pbc-integral-injective-lying-over; Tag 00GQ). Together with step 4 this
   proves existence and uniqueness for every base prime. -/
theorem radicial_prime_unique_degree_p
    (R : Type u) [CommRing R] [IsDomain R] (p : ℕ) (hp : p.Prime)
    (hchar : (p : R) = 0) (f : R) [IsDomain (AdjoinRoot (X ^ p - C f))] :
    Function.Injective (of (X ^ p - C f)) ∧
      (∀ c : AdjoinRoot (X ^ p - C f), IsIntegral R c) ∧
      (∀ c : AdjoinRoot (X ^ p - C f), c ^ p ∈ (of (X ^ p - C f)).range) ∧
      (∀ P : Ideal R, P.IsPrime →
        ∃! Q : Ideal (AdjoinRoot (X ^ p - C f)),
          Q.IsPrime ∧ Q.comap (of (X ^ p - C f)) = P) := by
  let g : R[X] := X ^ p - C f
  have hg : g.Monic := by
    dsimp [g]
    exact monic_X_pow_sub_C f hp.ne_zero
  have hpdeg : g.degree ≠ 0 := by
    rw [degree_X_pow_sub_C hp.pos]
    simp [hp.ne_zero]
  have hinj : Function.Injective (of g) := of.injective_of_degree_ne_zero hpdeg
  have hfin : Module.Finite R (AdjoinRoot g) := hg.finite_adjoinRoot
  have hint : Algebra.IsIntegral R (AdjoinRoot g) := Algebra.IsIntegral.of_finite R _
  have hcharP : CharP R p := (CharP.charP_iff_prime_eq_zero hp).2 hchar
  let : Fact p.Prime := ⟨hp⟩
  let : CharP R p := hcharP
  let : CharP (AdjoinRoot g) p := (CharP.charP_iff_prime_eq_zero hp).2 (by
    change ((p : R) : AdjoinRoot g) = 0
    rw [hchar]
    exact map_zero (of g))
  have hpow : ∀ c : AdjoinRoot g, c ^ p ∈ (of g).range := by
    intro c
    induction c using AdjoinRoot.induction_on with
    | ih q =>
      induction q using Polynomial.induction_on' with
      | add q r hq hr =>
          rw [map_add, add_pow_char]
          rcases hq with ⟨a, ha⟩
          rcases hr with ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          rw [map_add, ← ha, ← hb]
      | monomial n a =>
          refine ⟨a ^ p * f ^ n, ?_⟩
          have hz : root g ^ p = of g f := by
            have := eval₂_root g
            apply sub_eq_zero.mp
            simpa [g, eval₂_sub, eval₂_pow] using this
          rw [← aeval_eq, aeval_def, eval₂_monomial]
          simp only [map_pow, map_mul]
          rw [AdjoinRoot.algebraMap_eq]
          rw [mul_pow, ← pow_mul, Nat.mul_comm n p, pow_mul, hz]
  have hhomeo : IsHomeomorph (PrimeSpectrum.comap (of g)) := by
    apply PrimeSpectrum.isHomeomorph_comap
    · intro x
      exact ⟨p, hp.pos, hpow x⟩
    · exact (RingHom.injective_iff_ker_eq_bot (of g)).1 hinj ▸ bot_le
  refine ⟨hinj, ?_, hpow, ?_⟩
  · intro c; exact hint.isIntegral c
  · intro P hP
    obtain ⟨q, hq⟩ := hhomeo.surjective ⟨P, hP⟩
    refine ⟨q.asIdeal, ⟨q.isPrime, ?_⟩, ?_⟩
    · exact congrArg (fun z : PrimeSpectrum R => z.asIdeal) hq
    · intro Q hQ
      let qQ : PrimeSpectrum (AdjoinRoot g) := ⟨Q, hQ.1⟩
      have hqQ : PrimeSpectrum.comap (of g) qQ = ⟨P, hP⟩ := by
        exact PrimeSpectrum.ext hQ.2
      have : qQ = q := hhomeo.injective (hqQ.trans hq.symm)
      exact congrArg (fun z : PrimeSpectrum (AdjoinRoot g) => z.asIdeal) this
end AdjoinRoot
