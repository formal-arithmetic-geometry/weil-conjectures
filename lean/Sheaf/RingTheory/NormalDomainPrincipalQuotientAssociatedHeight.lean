/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
import Sheaf.RingTheory.AssociatedPrimeLocalizeAtPrime
import Sheaf.RingTheory.Depth
import Sheaf.RingTheory.DepthInSES
import Sheaf.RingTheory.DepthLeDimAssociatedPrime
import Sheaf.RingTheory.SerreConditions
import Sheaf.RingTheory.SerreCriterionNormal

/-!
# Associated primes of principal quotients of normal domains

Source: Stacks Project, Algebra, Tag 031T, Lemma 10.157.6 (1)
(blueprint: lem-weil-pbc-normal-domain-principal-quotient-associated-height).
-/

@[expose] public section

universe u

namespace Ideal

/-- Every associated prime of a nonzero principal quotient of a Noetherian normal domain
has height one. Source: Stacks Project, Algebra, Tag 031T, Lemma 10.157.6 (1)
(blueprint: lem-weil-pbc-normal-domain-principal-quotient-associated-height).

Since `A` is Noetherian, `isAssociatedPrime_iff` identifies association with being the
annihilator of an element; primality forces that element to be nonzero. For a prime,
`Ideal.height` is the supremum of lengths of strict prime chains ending at that prime.

Proof following the six steps of the node:
1. The element `a` annihilates every element of `A/aA`, hence belongs to `p`. Since `a`
   is nonzero and `A` is a domain, the prime chain `(0) < p` gives height at least one.
2. By `lem-weil-pbc-localization-normal-domain`, all prime localizations are normal domains.
   Serre's criterion `lem-weil-pbc-serre-criterion-normal` gives condition `(S₂)`
   (`def-weil-pbc-serre-conditions-rk-sk`), so depth at `p` is at least `min(2, dim A_p)`.
3. Multiplication by `a` is injective. Localize the exact sequence
   `0 → A → A → A/aA → 0` using `lem-weil-pbc-localization-module-exact` and
   `def-weil-pbc-module-localization`. The ring `A_p` is Noetherian by
   `lem-weil-pbc-localization-noetherian`, and local by
   `def-weil-pbc-localization-at-prime`. The quotient is finite and nonzero since `a ∈ p`.
4. The depth inequality `lem-weil-pbc-depth-in-ses` (2), with `def-weil-pbc-depth`,
   implies depth of `(A/aA)_p` is at least one if `dim A_p ≥ 2`.
5. By `lem-weil-pbc-associated-prime-localize-at-prime`, the localized annihilator
   is the maximal ideal. The bound `lem-weil-pbc-depth-le-dim-associated-prime` gives
   depth at most the dimension of the residue field, which is zero
   (`def-weil-pbc-krull-dimension-ring`). Thus the localized quotient has depth zero.
6. Consequently `dim A_p ≤ 1`. By
   `lem-weil-pbc-localization-dimension-chains-below-prime`, no strict prime chain
   ending at `p` has length at least two. Together with step 1 this gives height one.
-/
theorem height_eq_one_of_mem_associatedPrimes_quotient_span
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {a : A} (ha : a ≠ 0) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {a})) :
    p.height = 1 := by
  sorry

end Ideal
