/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.Algebra.Regular.SMul

/-!
# A nonzerodivisor in the maximal ideal

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 00LL
(blueprint: lem-weil-pbc-nonzerodivisor-if-maximal-not-associated).
-/

universe u v

/-- (blueprint: lem-weil-pbc-nonzerodivisor-if-maximal-not-associated)
Let `R` be a Noetherian local commutative ring and `M` a finite `R`-module.
If the maximal ideal is not an associated prime of `M`, then it contains an
element acting injectively on `M`. "Not an associated prime" is Mathlib's
`associatedPrimes`; "nonzerodivisor on `M`" is `IsSMulRegular M x`.
Source: Algebra, Tag 00LL.

Proof (Stacks, Algebra, Tag 00LL, implication (2) => (1) for `I = m`):
the associated primes of `M` are finite. Every associated prime is proper,
thus is contained in the maximal ideal; the hypothesis excludes equality,
so the maximal ideal is contained in none of them. Prime avoidance supplies
an element of the maximal ideal outside their union (and `0` does so when
the union is empty). The union-of-associated-primes characterization of
zero divisors then shows that this element acts injectively on `M`.
-/
theorem exists_mem_maximalIdeal_smul_injective
    (R : Type u) (M : Type v) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : IsLocalRing.maximalIdeal R ∉ associatedPrimes R M) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧ IsSMulRegular M x := by
  sorry
