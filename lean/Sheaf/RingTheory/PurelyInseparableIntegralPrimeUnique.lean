/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Prime

/-!
# Unique primes in a finite purely inseparable integral extension

Source: literature/stacks-project/more-algebra.tex, Lemma Tag 07PR
(blueprint: lem-weil-pbc-purely-inseparable-integral-prime-unique).
-/

universe u v w x

/-- Source: Stacks Project, More on Algebra, Lemma Tag 07PR, proof, and Algebra,
Tag 0BR8 (blueprint: lem-weil-pbc-purely-inseparable-integral-prime-unique).
A finite extension of domains with normal base and finite purely inseparable fraction fields
has exactly one prime above each base prime.

Proof: First, for every `b` in `B`, pure inseparability gives a power `b^(e^n)` in `K`,
where `e` is the exponential characteristic. This power remains in `B`, hence is integral
 over `A` by finite generation (lem-weil-pbc-finite-algebra-is-integral). Its monic equation
holds in `K` because `K → L` is injective. Normality of `A`
(def-weil-pbc-normal-ring and def-weil-pbc-integral-closure) puts the power in `A`.
Second, the map `A → B` is injective and integral, so lying over
(lem-weil-pbc-integral-injective-lying-over) supplies a prime over `p`.
Third, if two primes lie over `p`, a power of any element in the first lies in `A`,
hence in `p` and the second prime. Primality puts the element itself in the second.
Exchanging the primes gives equality. In characteristic zero `e = 1`, so the same
argument applies without imposing positive characteristic. -/
theorem purelyInseparable_integral_prime_unique
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B] (hA : IsIntegrallyClosed A)
    [Module.Finite A B]
    (K : Type w) (L : Type x) [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra A L]
    [Algebra K L] [IsScalarTower A K L] [IsScalarTower A B L]
    [Module.Finite K L] [IsPurelyInseparable K L]
    (p : Ideal A) [p.IsPrime] :
    ∃! q : Ideal B, q.IsPrime ∧ q.comap (algebraMap A B) = p := by
  sorry
