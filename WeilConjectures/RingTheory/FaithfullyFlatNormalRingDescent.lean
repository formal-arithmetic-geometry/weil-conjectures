/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
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

private theorem integrallyClosed_of_faithfullyFlat
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] [IsDomain B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A := by
  let : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain (algebraMap A B)
  let K := FractionRing A
  let L := FractionRing B
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A B L]
    exact (IsFractionRing.injective B L).comp (FaithfulSMul.algebraMap_injective A B)
  let f : K →ₐ[A] L := IsFractionRing.liftAlgHom (g := Algebra.ofId A L) hinj
  apply (isIntegrallyClosed_iff K).mpr
  intro x hx
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    ((hx.map f).tower_top (A := B))
  have hbL : algebraMap B L (algebraMap A B b) ≠ 0 := by
    exact fun h ↦ hb0 ((IsFractionRing.injective B L).comp
      (FaithfulSMul.algebraMap_injective A B) (by simpa using h))
  have heq : algebraMap A B a = algebraMap A B b * s := by
    apply IsFractionRing.injective B L
    have hs' : algebraMap B L s =
        algebraMap B L (algebraMap A B a) / algebraMap B L (algebraMap A B b) := by
      simpa only [← hab, map_div₀, AlgHom.commutes, ← IsScalarTower.algebraMap_apply A B L] using hs
    rw [map_mul, hs', mul_div_cancel₀ _ hbL]
  have ha : a ∈ Ideal.span ({b} : Set A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span ({b} : Set A))]
    change algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span ({b} : Set A))
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact ⟨s, heq⟩
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
  refine ⟨r, ?_⟩
  rw [← hab, hr, map_mul, mul_div_cancel_left₀]
  exact fun h ↦ hb0 ((IsFractionRing.injective A K) (by simpa using h))

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
  intro p hp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := S) p
  let := hq
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q
  have hpq : p = q.comap (algebraMap R S) := hqp.over
  let f : A →+* B := Localization.localRingHom p q (algebraMap R S) hpq
  let : Algebra A B := f.toAlgebra
  let : Module.Flat A B :=
    (RingHom.Flat.localRingHom ((RingHom.flat_algebraMap_iff).mpr inferInstance) q p hpq)
  let : IsLocalHom (algebraMap A B) :=
    Localization.isLocalHom_localRingHom p q (algebraMap R S) hpq
  let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  obtain ⟨hd, hi⟩ := hS q
  let : IsDomain B := hd
  let : IsIntegrallyClosed B := hi
  exact ⟨(FaithfulSMul.algebraMap_injective A B).isDomain (algebraMap A B),
    integrallyClosed_of_faithfullyFlat A B⟩

end Algebra
