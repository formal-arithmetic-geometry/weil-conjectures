/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Universal catenarity checked on minimal-prime quotients

Source: Stacks Project, Algebra, Tag 0AUP, `lemma-catenary-check-irreducible`, clause (2)
(blueprint: lem-per-universal-catenarity-minimal-quotients).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A Noetherian ring is universally catenary if and only if every quotient by a minimal
prime ideal is universally catenary. Source: Stacks Project, Algebra, Tag 0AUP,
`lemma-catenary-check-irreducible`, clause (2)
(blueprint: lem-per-universal-catenarity-minimal-quotients).

Proof (the source omits the reverse direction):
1. If A is universally catenary, its quotient by any minimal prime is universally
   catenary by `lem-per-universal-catenarity-quotient` (Stacks Tag 00NK).
2. Conversely, let B be any finite type A-algebra, and fix primes q <= r of B. Contract
   q to A and use `lem-weil-pbc-prime-contains-minimal-prime` to choose a minimal prime
   p below that contraction. The contraction is prime because inverse images under
   unital ring homomorphisms preserve primality.
3. Set J = pB and C = B/J. Then J <= q. Reduce finite algebra generators of B modulo J
   to see that C is finite type over A/p, using `def-weil-pbc-finite-type-algebra`.
   The hypothesis on p and `def-exc-excellent-ring` make C catenary.
4. By `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`, contraction along B -> C
   identifies primes of C with primes of B containing J, with inverse given by ideal
   image. These inverse monotone maps restrict to an order isomorphism from [q,r]
   to the corresponding prime interval in C, since every member of [q,r] contains J.
5. The interval isomorphism preserves strict chains, their lengths and saturation:
   an intermediate prime can be inserted on one side exactly when it can on the other.
   Transfer the finite chain-length bound and equality of saturated-chain lengths from
   C to [q,r]. Thus B is catenary, and A is universally catenary by
   `def-exc-excellent-ring`. Equal endpoints give length zero; no primes makes the
   condition vacuous.
-/
theorem isUniversallyCatenary_iff_quotient_minimalPrimes
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    IsUniversallyCatenary A ↔
      ∀ p : Ideal A, p ∈ minimalPrimes A → IsUniversallyCatenary (A ⧸ p) := by
  sorry
