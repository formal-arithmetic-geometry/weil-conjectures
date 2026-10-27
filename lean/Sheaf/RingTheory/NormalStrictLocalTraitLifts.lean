/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.ValuationRingNormal
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Dominant compatible strict henselizations of a normal local domain and a trait

Source: Stacks Project, Algebra, Tags 04GU, 04GW and 08HR; More on Algebra,
Tags 06DI and 07QM (blueprint: lem-sfb-normal-strict-local-trait-lifts).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Algebra

/-- Compatible strict henselizations preserve the given dominant local trait map.
Source: Stacks Project, Tags 04GU, 04GW, 08HR, 06DI and 07QM
(blueprint: lem-sfb-normal-strict-local-trait-lifts).

Proof:
1. By def-weil-pbc-relative-separable-closure, the relative separable closures in Omega
   are separable closures. A separable polynomial over k stays separable over l, since
   its Bezout identity with its derivative survives scalar extension. This gives tau.
2. The pointed etale pairs in def-sc-ring-strict-henselization are equivalent to the
   triples in lem-weil-pbc-strict-henselization-triples: take the kernel of a pointing
   and extend the induced injection on the quotient to its fraction field. The inverse
   composes with the residue map. Transport the colimit and its pointing maps through
   this equivalence. The triples lemma gives strict henselianity, locality, surjective
   residue maps with maximal-ideal kernels, and the displayed residue identifications.
3. The field case for R is immediate. In the DVR case, valuation arithmetic gives
   v(x) + v(1/x) = 0; lem-sc-dvr-nonnegative-valuation-in-ring then gives x or 1/x in R.
   Apply lem-weil-pbc-valuation-ring-normal. The lemma
   lem-weil-pbc-localization-normal-domain makes A and R normal at every prime.
4. Apply lem-weil-pbc-etale-colimit-normal-local-domain to the two presentations.
   It gives normal domains H and B and injective structure maps A to H and R to B.
5. Apply lem-weil-pbc-map-into-henselian-colimit with base A, target B and source H.
   Locality of the given maps checks contraction of maximal ideals. Its prescribed
   residue map is tau, so it gives the unique local extension with that residue map.
6. For z = x/y in Frac H, use lem-weil-pbc-filtered-colimit-algebras-elementwise to
   represent x and y at one etale stage S. The prime q = ker(S to H) lies over zero.
   By lem-weil-pbc-etale-algebra-residue-field-separable, kappa(q) is finite separable
   over Frac A and embeds in Frac H. The element z is in this image, hence algebraic.
7. If nonzero x in H were killed by h, remove the initial power of X from a nonzero
   polynomial relation for x over Frac A. Its constant coefficient is nonzero. Clear
   denominators to get a relation over A with nonzero constant coefficient. Applying
   h kills that coefficient, contradicting injectivity of A to R to B.
8. The map on spectra is contraction of prime ideals. Injectivity sends the generic
   point to the generic point, and locality sends the closed point to the closed point.
   Composing the residue equation with the inclusions into Omega gives equality of
   the closed geometric evaluations; contravariant Spec gives the final scheme square.
No Noetherian hypothesis is used. -/
theorem normal_strict_local_trait_lifts
    (A : Type u) (R : Type v) (Ω H B : Type (max u v w))
    [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing R] [IsLocalRing R] [IsDomain R]
    (hR : IsField R ∨ IsDiscreteValuationRing R)
    [Algebra A R]
    (hf : Function.Injective (algebraMap A R))
    (hf_local : (IsLocalRing.maximalIdeal R).comap (algebraMap A R) =
      IsLocalRing.maximalIdeal A)
    [Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R)]
    (hres : (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R)).comp
      (IsLocalRing.residue A) = (IsLocalRing.residue R).comp (algebraMap A R))
    [Field Ω] [IsAlgClosed Ω]
    [Algebra (IsLocalRing.ResidueField A) Ω]
    [Algebra (IsLocalRing.ResidueField R) Ω]
    [IsScalarTower (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField R) Ω]
    [CommRing H] [Algebra A H] [CommRing B] [Algebra R B]
    [Algebra A (separableClosure (IsLocalRing.ResidueField A) Ω)]
    [IsScalarTower A (IsLocalRing.ResidueField A)
      (separableClosure (IsLocalRing.ResidueField A) Ω)]
    [Algebra R (separableClosure (IsLocalRing.ResidueField R) Ω)]
    [IsScalarTower R (IsLocalRing.ResidueField R)
      (separableClosure (IsLocalRing.ResidueField R) Ω)]
    (P : StrictHenselizationPresentationIn.{u, max v w} A
      (separableClosure (IsLocalRing.ResidueField A) Ω) H)
    (Q : StrictHenselizationPresentationIn.{v, max u w} R
      (separableClosure (IsLocalRing.ResidueField R) Ω) B) :
    ∃ (_ : IsStrictlyHenselianLocalRing H) (_ : IsStrictlyHenselianLocalRing B)
      (_ : IsDomain H) (_ : IsDomain B),
      IsIntegrallyClosed H ∧ IsIntegrallyClosed B ∧
      (∃ eH : IsLocalRing.ResidueField H ≃+* separableClosure (IsLocalRing.ResidueField A) Ω,
        eH.toRingHom.comp (IsLocalRing.residue H) = P.residueMap) ∧
      (∃ eB : IsLocalRing.ResidueField B ≃+* separableClosure (IsLocalRing.ResidueField R) Ω,
        eB.toRingHom.comp (IsLocalRing.residue B) = Q.residueMap) ∧
      ∃ hAH : Function.Injective (algebraMap A H),
        Function.Injective (algebraMap R B) ∧
        (∀ z : FractionRing H, ∃ p : Polynomial (FractionRing A), p ≠ 0 ∧
          Polynomial.eval₂ (IsFractionRing.map (K := FractionRing A) (L := FractionRing H)
            hAH) z p = 0) ∧
        ∃ τ : separableClosure (IsLocalRing.ResidueField A) Ω →+*
            separableClosure (IsLocalRing.ResidueField R) Ω,
          (separableClosure (IsLocalRing.ResidueField R) Ω).subtype.comp τ =
            (separableClosure (IsLocalRing.ResidueField A) Ω).subtype ∧
          ∃ h : H →+* B,
            (IsLocalRing.maximalIdeal B).comap h = IsLocalRing.maximalIdeal H ∧
            h.comp (algebraMap A H) = (algebraMap R B).comp (algebraMap A R) ∧
            Q.residueMap.comp h = τ.comp P.residueMap ∧
            Function.Injective h ∧
            (∀ h' : H →+* B,
              (IsLocalRing.maximalIdeal B).comap h' = IsLocalRing.maximalIdeal H →
              h'.comp (algebraMap A H) = (algebraMap R B).comp (algebraMap A R) →
              Q.residueMap.comp h' = τ.comp P.residueMap → h' = h) ∧
            (Spec.map (CommRingCat.ofHom h))
                (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) =
              (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum H) ∧
            (Spec.map (CommRingCat.ofHom h))
                (⟨IsLocalRing.maximalIdeal B, inferInstance⟩ : PrimeSpectrum B) =
              (⟨IsLocalRing.maximalIdeal H, inferInstance⟩ : PrimeSpectrum H) ∧
            (separableClosure (IsLocalRing.ResidueField R) Ω).subtype.comp
                (Q.residueMap.comp h) =
              (separableClosure (IsLocalRing.ResidueField A) Ω).subtype.comp P.residueMap ∧
            Spec.map (CommRingCat.ofHom
                ((separableClosure (IsLocalRing.ResidueField R) Ω).subtype.comp Q.residueMap)) ≫
                Spec.map (CommRingCat.ofHom h) =
              Spec.map (CommRingCat.ofHom
                ((separableClosure (IsLocalRing.ResidueField A) Ω).subtype.comp P.residueMap)) := by
  sorry

end Algebra
