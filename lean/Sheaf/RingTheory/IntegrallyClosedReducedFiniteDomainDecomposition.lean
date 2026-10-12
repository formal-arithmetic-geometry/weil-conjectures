/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Sheaf.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Domain factors from integral closedness in total fractions

Source: Stacks Project, Algebra, Tag 030C, the idempotent argument.
(blueprint: lem-weil-pbc-integrally-closed-reduced-finite-domain-decomposition).
-/

@[expose] public section

universe u

/-- A reduced ring with finitely many minimal primes that is integrally closed in its
 total fraction ring splits into finitely many domains. This asserts no integral
 closedness of the factors.
Source: Stacks Project, Algebra, Tag 030C, proof, second and third paragraphs.
(blueprint: lem-weil-pbc-integrally-closed-reduced-finite-domain-decomposition).

Proof: enumerate the minimal primes p_i. The nonzerodivisors are precisely the complement
of their union. The primes disjoint from this set are exactly the minimal primes, by finite
prime avoidance. Their localizations are fields. The total fraction ring is reduced and
has just these finitely many maximal ideals, with intersection zero. The product of its
localizations is therefore its decomposition as the product of the fields R_{p_i}.
Each coordinate idempotent satisfies the monic polynomial T^2 - T, so integral closedness
lifts it uniquely to R. Injectivity of R into its total fractions shows that these lifted
idempotents are orthogonal and sum to one. Multiplication by them decomposes R into their
image rings: the forward map is r to (e_i r), and the inverse sums the components.
The i-th image ring embeds into R_{p_i}, because all its other coordinates vanish, and is
nonzero because its identity e_i has i-th coordinate one. It is thus a domain. Package the
image rings as CommRingCat objects indexed by Fin n. If there are no minimal primes, R is
the zero ring, which is the empty product. -/
theorem exists_finite_domain_factors_of_integrallyClosed_totalFractions
    (R : Type u) [CommRing R] [IsReduced R]
    (hfinite : (minimalPrimes R).Finite)
    (hclosed : IsIntegrallyClosedIn R (FractionRing R)) :
    ∃ (n : ℕ) (A : Fin n → CommRingCat.{u}),
      (∀ i : Fin n, IsDomain (A i)) ∧ Nonempty (R ≃+* (∀ i : Fin n, A i)) := by
  sorry
