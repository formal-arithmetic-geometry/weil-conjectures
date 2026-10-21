/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat

/-!
# Faithfully flat descent of normal rings

Source: Stacks Project, Algebra, Tag 033G (lemma-descent-normal)
(blueprint: lem-sfb-faithfully-flat-normal-ring-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Normality descends along any faithfully flat map of commutative rings, including
non-Noetherian rings and the zero ring. Normality is the assertion that every prime
localization is an integrally closed domain.

Source: Stacks Project, Algebra, Tag 033G (lemma-descent-normal)
(blueprint: lem-sfb-faithfully-flat-normal-ring-descent).

Proof:
1. Fix a prime p of R. By lem-weil-pbc-faithfully-flat-surjective-spectrum choose a
   prime q of S lying over p, using def-weil-pbc-faithfully-flat-ring-map.
2. By lem-weil-pbc-flat-local-ring-maps the induced map g : R_p -> S_q is flat and
   local. Hence lem-weil-pbc-flat-local-hom-faithfully-flat makes it faithfully flat.
   The hypothesis and def-weil-pbc-normal-ring say that S_q is an integrally closed
   domain. The optional Noetherian clause of the localization lemma is not used.
3. Apply lem-weil-pbc-faithfully-flat-ideal-contraction with the zero ideal to see
   that g is injective. Thus R_p is a domain, since S_q is a domain.
4. If x = a/b in Frac(R_p), b nonzero, is integral over R_p, the injective map g
   induces an injective map Frac(R_p) -> Frac(S_q). Transporting a monic equation
   shows that g(a)/g(b) is integral over S_q. Integral closedness gives s in S_q
   with g(a)/g(b) = s, whence g(a) = g(b)s.
5. The extension of the ideal bR_p is g(b)S_q. By
   lem-weil-pbc-faithfully-flat-ideal-contraction, a belongs to bR_p. Write a = br;
   then x = r/1 belongs to R_p.
6. Thus R_p is an integrally closed domain for every prime p, exactly normality
   by def-weil-pbc-normal-ring. For R = 0 there are no primes, so the conclusion
   is vacuous; unitality forces S = 0. Conversely faithful flatness into the zero
   ring forces R = 0 by injectivity. No domain assumption on R itself is used. -/
theorem normal_ring_of_faithfullyFlat
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S]
    (hS : ∀ (q : Ideal S) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q)) :
    ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  sorry

end Algebra
