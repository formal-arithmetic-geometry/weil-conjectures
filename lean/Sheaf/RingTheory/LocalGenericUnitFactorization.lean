/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight
import WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes

/-! # Units on an integral generic fibre

Source: Stacks Project, Divisors, Tag 0BD7, proof of lemma-in-image-pullback,
affine factorization and subsequent local uniqueness paragraphs
(blueprint: lem-sfb-local-generic-unit-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Algebra

/-- For a flat local map of Noetherian domains with normal base and integral nonempty
fibres, every generic-fibre unit factors as a base fraction times a target unit.
The base factor is unique modulo base units, and a base fraction is a target unit
exactly when it is a base unit. The generic fibre is `FractionRing A ⊗[A] B`, canonically
`(A ∖ {0})⁻¹B`; `Ideal.Fiber` is the localization of `B/pB` at the images of `A ∖ p`.

Source: Stacks Project, Divisors, Tag 0BD7, proof of lemma-in-image-pullback
(blueprint: lem-sfb-local-generic-unit-factorization).

Proof following the ten steps of the node:
1. The local flat map is faithfully flat, by
   `lem-weil-pbc-flat-module-faithfully-flat-maximal-ideals`. Its residue quotient is
   nonzero because the extended base maximal ideal lies in the target maximal ideal.
   `lem-weil-pbc-faithfully-flat-ideal-contraction` gives ideal contraction and injectivity.
2. For each prime p, flat tensor exactness (`lem-weil-pbc-flat-tensor-exact`) makes B/pB
   torsion-free over A/p. Thus it injects into the assumed nonzero integral fibre.
   Consequently pB is prime and contracts to p.
3. Write f = a/r and its inverse as a'/r', so aa' = rr' = t is nonzero.
   `lem-sc-finite-minimal-primes-over-ideal` gives finitely many minimal primes p_i
   over t. By `lem-sfb-krull-principal-ideal-height-bound` they have height one.
   `lem-trf-normal-domain-principal-divisor-kernel` makes A_(p_i) DVRs. When t is a
   unit the list is empty, and all intersections below are the whole ring.
4. Put q_i = p_i B. The localizations B_(q_i) are Noetherian local domains
   (`lem-weil-pbc-localization-noetherian`, `def-weil-pbc-localization-at-prime`).
   A uniformizer pi_i of A_(p_i) generates their maximal ideal. Apply
   `lem-weil-pbc-dvr-unit-times-uniformizer-power` to a and a' there, with exponents
   e_i and e'_i. Cancellation gives e_i + e'_i = v_(p_i)(t).
5. The intersection of the symbolic powers p_i^(e_i+e'_i) is (t). Indeed,
   `lem-weil-pbc-normal-domain-principal-quotient-associated-height` puts every
   associated prime of A/tA in the list. Then
   `lem-weil-pbc-module-injects-localizations-associated-primes` detects membership in (t).
6. Set I = intersection p_i^(e_i) and I' = intersection p_i^(e'_i). Localizing products
   shows II' is contained in (t), by step 5.
7. Flat tensor exactness preserves finite intersections of ideals, using the map to
   the finite sum of quotients. By `lem-sfb-symbolic-powers-flat-prime-extension`,
   IB and I'B are the intersections of the corresponding symbolic powers of q_i.
   Thus a belongs to IB and a' belongs to I'B.
8. Since aa' = t, extension gives (II')B = tB. Faithful-flat contraction gives II' = (t).
   Write t as a finite sum x_j y_j with x_j in I and y_j in I', and x_j y_j = c_j t.
   Cancellation gives sum c_j = 1. Some c_j is a unit by locality. Rescaling this
   pair gives gg' = t. Cancelling g' shows I = (g), and similarly I' = (g').
9. Write a = gu and a' = g'u'. Cancelling t in aa' = gg' gives uu' = 1.
   Thus u is a target unit and h = g/r is a nonzero base fraction, with f = hu.
10. If h = c/d is a target unit, contraction of dB and cB shows both h and its
    inverse belong to A, so h is a base unit. The converse maps an inverse.
    If hu = h'u', then h/h' = u'/u is a target unit, and reflection proves uniqueness.
-/
theorem local_generic_unit_factorization
    (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsIntegrallyClosed A] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hflat : RingHom.Flat (algebraMap A B))
    (hfibres : ∀ (p : Ideal A) [p.IsPrime], IsDomain (p.Fiber B)) :
    (∀ f : (FractionRing A ⊗[A] B)ˣ,
      ∃ (h : (FractionRing A)ˣ) (w : Bˣ),
        (f : FractionRing A ⊗[A] B) =
          algebraMap (FractionRing A) (FractionRing A ⊗[A] B) h *
            Algebra.TensorProduct.includeRight (R := A) (A := FractionRing A) (w : B)) ∧
    (∀ (h h' : (FractionRing A)ˣ) (w w' : Bˣ),
      algebraMap (FractionRing A) (FractionRing A ⊗[A] B) h *
          Algebra.TensorProduct.includeRight (R := A) (A := FractionRing A) (w : B) =
        algebraMap (FractionRing A) (FractionRing A ⊗[A] B) h' *
          Algebra.TensorProduct.includeRight (R := A) (A := FractionRing A) (w' : B) →
      ∃ a : Aˣ, algebraMap A (FractionRing A) a = (h : FractionRing A) / h') ∧
    (∀ h : (FractionRing A)ˣ,
      (∃ w : Bˣ, algebraMap (FractionRing A) (FractionRing A ⊗[A] B) h =
        Algebra.TensorProduct.includeRight (R := A) (A := FractionRing A) (w : B)) ↔
      ∃ a : Aˣ, algebraMap A (FractionRing A) a = h) := by
  sorry

end Algebra
