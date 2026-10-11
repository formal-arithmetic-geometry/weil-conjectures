/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Normality and total fractions of a reduced ring

Source: Stacks Project, Algebra, Lemma Tag 030C
(blueprint: lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions).

`FractionRing R` is localization at `nonZeroDivisors R`, the ring specialization of
`def-weil-pbc-module-localization`. Normality uses the inline prime-localization
condition recorded by `def-weil-pbc-normal-ring`. The empty finite product is allowed.
-/

@[expose] public section

universe u

/-- For a reduced ring with finitely many minimal primes, normality, integral closedness
in the total fraction ring, and being a finite product of normal domains are equivalent.
Source: Stacks Project, Algebra, Lemma Tag 030C
(blueprint: lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions).

Proof (the five steps of the node):
1. The nonzerodivisors are the complement of the union of the minimal primes by
   `lem-weil-pbc-reduced-zerodivisors-union-minimal-primes`. Localization-prime
   correspondence (`lem-weil-pbc-localization-prime-residue-field-iso`) and
   `lem-weil-pbc-prime-avoidance` identify the primes of Q(R) with these minimal primes.
   Their localizations are fields by `lem-weil-pbc-minimal-prime-reduced-localization-field`.
   The total fraction ring is reduced: clearing a nonzerodivisor denominator in a nilpotent
   equation gives a nilpotent numerator, hence zero. Its finitely many maximal ideals
   therefore have intersection zero by `lem-weil-pbc-zero-locus-eq-iff-radical-eq`.
   Apply `lem-weil-pbc-product-of-localizations-at-maximal` to obtain
   Q(R) = product of the fields R_p. With no minimal primes, R is the zero ring.
2. Normality implies integral closedness by `lem-weil-pbc-normal-ring-integrally-closed-total`:
   an integral total fraction belongs locally to every normal domain R_p. The ideal of
   coefficients a for which ax belongs to R has an element outside every prime ideal,
   hence is the unit ideal. Taking a = 1 shows x belongs to R.
3. If R is integrally closed in Q(R), its coordinate idempotents belong to R because
   they satisfy T^2 - T = 0. These orthogonal idempotents sum to 1, and multiplication
   by them decomposes R into their image rings, with inverse given by summing coordinates.
   Each image is R/p for the corresponding minimal prime, hence a domain; its fraction
   field is R_p by `lem-weil-pbc-minimal-prime-reduced-localization-field`.
4. Transport integral closedness through these decompositions. By
   `lem-weil-pbc-finite-product-integral-closure`, each factor is integrally closed in
   its fraction field, so each factor is a normal domain. This proves (2) implies (3).
5. `lem-weil-pbc-finite-product-normal` proves (3) implies (1): each prime localization
   of the finite product is a prime localization of one normal factor. Together with
   step 2 this gives both equivalences below. -/
theorem reduced_normal_iff_integrallyClosed_totalFractions
    (R : Type u) [CommRing R] [IsReduced R]
    (hfinite : (minimalPrimes R).Finite) :
    ((∀ (p : Ideal R) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
      IsIntegrallyClosedIn R (FractionRing R)) ∧
    (IsIntegrallyClosedIn R (FractionRing R) ↔
      ∃ (n : ℕ) (A : Fin n → CommRingCat.{u}),
        (∀ i : Fin n, IsDomain (A i) ∧ IsIntegrallyClosed (A i)) ∧
          Nonempty (R ≃+* (∀ i : Fin n, A i))) := by
  sorry
