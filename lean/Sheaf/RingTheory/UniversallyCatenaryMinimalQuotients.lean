/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.UniversallyCatenaryQuotient

/-!
# Universal catenarity checked on minimal-prime quotients

Source: Stacks Project, Algebra, Tag 0AUP, lemma-catenary-check-irreducible, clause (2)
(blueprint: lem-per-universal-catenarity-minimal-quotients).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A Noetherian ring is universally catenary if and only if its quotient by every
minimal prime is universally catenary.

Source: Stacks Project, Algebra, Tag 0AUP, lemma-catenary-check-irreducible, clause (2)
(blueprint: lem-per-universal-catenarity-minimal-quotients).

Proof (the source omits the proof of clause (2); the DAG supplies this argument):
1. If A is universally catenary, apply lem-per-universal-catenarity-quotient to each
   minimal prime p. This gives universal catenarity of A/p.
2. Conversely, suppose all these quotients are universally catenary. Unpack
   def-exc-excellent-ring: for every finite type A-algebra B we must prove catenarity.
   Fix primes q ≤ r of B. Their lower endpoint contracts to a prime a of A:
   the contraction is proper, and primality follows by applying the ring map to a
   product. By lem-weil-pbc-prime-contains-minimal-prime with I = 0, choose a minimal
   prime p ≤ a.
3. Let J = pB, so J ≤ q, and C = B/J. The induced map A/p → C makes C finite type:
   reduce a finite set of algebra generators of B and all polynomial coefficients
   modulo p, using def-weil-pbc-finite-type-algebra. Thus C is catenary by the
   hypothesis on p and def-exc-excellent-ring.
4. By lem-weil-pbc-spec-quotient-homeomorphism-zero-locus, primes of C correspond
   bijectively to primes of B containing J, by contraction and image under the
   quotient map. Both maps preserve and reflect inclusion. Since J ≤ q, they give
   an order isomorphism of the prime intervals with endpoints q, r and their images.
5. Apply this correspondence member by member to finite strict chains. It preserves
   strict inclusions and length. An intermediate prime exists on one side exactly
   when one exists on the other, so saturation is preserved too. The finite bound
   and common length of saturated chains in C transfer to the interval in B.
   This proves B catenary, hence A universally catenary. Equal endpoints give length
   zero; the condition on a ring with no primes is vacuous. -/
theorem isUniversallyCatenary_iff_quotient_minimalPrimes
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    IsUniversallyCatenary A ↔
      ∀ p : Ideal A, p ∈ minimalPrimes A → IsUniversallyCatenary (A ⧸ p) := by
  sorry
