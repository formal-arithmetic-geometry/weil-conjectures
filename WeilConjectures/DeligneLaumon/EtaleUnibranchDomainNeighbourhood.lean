/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.RingTheory.StrictHenselizationPresentationIn
import WeilConjectures.DeligneLaumon.EtaleGenericReducedComponents
import WeilConjectures.DeligneLaumon.EtaleUnibranchLocalStalkDomain
import WeilConjectures.DeligneLaumon.ReducedFiniteMinimalPrimeDomainLocalization
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! # Domain neighbourhood in an etale algebra over a geometrically unibranch domain

Source: Stacks Project, `more-algebra.tex`, Tag 0GSC, lemma
`lemma-local-unramified-extension-unibranch-domain-is-etale`, proof (blueprint:
lem-dl-a1-etale-unibranch-domain-neighbourhood).

## Main statement

* `etale_unibranch_domain_neighbourhood` gives a principal localization of an etale
  algebra at a prime which is a domain when the corresponding base localization is
  geometrically unibranch.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry

/-- An etale algebra over a domain has a domain principal neighbourhood at a prime over a
geometrically unibranch localization of the base.

Source: Stacks Project, `more-algebra.tex`, Tag 0GSC, lemma
`lemma-local-unramified-extension-unibranch-domain-is-etale`, proof, the paragraph reducing
an etale algebra to a domain (blueprint: lem-dl-a1-etale-unibranch-domain-neighbourhood).

Proof (the three proof steps of the DAG node):
1. The generic-component lemma for an etale algebra over a domain gives that `C` is reduced,
   has finitely many minimal primes, and each minimal prime contracts to `(0)` in `A`.
2. The etale local-domain lemma gives that `C_Q` is a domain under the geometric-unibranch
   hypothesis on `A_p`. Prime correspondence for localization shows that exactly one minimal
   prime of `C` is contained in `Q`.
3. The reduced finite-minimal-prime localization lemma then supplies `h ∉ Q` for which
   `C[1/h]` is a domain.
-/
theorem etale_unibranch_domain_neighbourhood
    (A C : Type u) [CommRing A] [CommRing C] [IsDomain A] [Algebra A C]
    (hEtale : Etale
      (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (Q : Ideal C) [Q.IsPrime] (p : Ideal A) [p.IsPrime]
    (hp : Q.comap (algebraMap A C) = p)
    (hgeom : ∀ (K H : Type (max u v)) [Field K]
      [Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
      [IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
      [Algebra (Localization.AtPrime p) K]
      [IsScalarTower (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p)) K]
      [CommRing H] [Algebra (Localization.AtPrime p) H],
      Algebra.StrictHenselizationPresentationIn.{u, v}
          (Localization.AtPrime p) K H →
        IrreducibleSpace (PrimeSpectrum H)) :
    ∃ h : C, h ∉ Q ∧ IsDomain (Localization.Away h) := by
  obtain ⟨hred, hfin, _⟩ := etale_generic_reduced_components hEtale
  have : _root_.IsReduced C := hred
  have : IsDomain (Localization.AtPrime Q) :=
    etale_unibranch_local_stalk_domain A C hEtale Q p hp hgeom
  have hkernel (P : Ideal C) (hP : P ∈ minimalPrimes C) (hPQ : P ≤ Q) :
      P = (⊥ : Ideal (Localization.AtPrime Q)).comap
        (algebraMap C (Localization.AtPrime Q)) := by
    have : P.IsPrime := hP.isPrime
    have hcomap := Ideal.under_map_of_isLocalizationAtPrime
      (S := Localization.AtPrime Q) Q hPQ
    have hmap' : P.map (algebraMap C (Localization.AtPrime Q)) ∈
        ((⊥ : Ideal C).map (algebraMap C (Localization.AtPrime Q))).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q)]
      change (P.map (algebraMap C (Localization.AtPrime Q))).under C ∈ minimalPrimes C
      rwa [hcomap]
    have hmap : P.map (algebraMap C (Localization.AtPrime Q)) ∈
        minimalPrimes (Localization.AtPrime Q) := by
      simpa only [Ideal.map_bot] using hmap'
    have hzero : P.map (algebraMap C (Localization.AtPrime Q)) = ⊥ := by
      simpa only [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] using hmap
    simpa [hzero] using hcomap.symm
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal C))
    (J := Q) bot_le
  apply exists_away_domain_of_reduced_of_finite_minimalPrimes C hfin Q
  refine ⟨P, ⟨hP, hPQ⟩, ?_⟩
  intro P' hP'
  exact (hkernel P' hP'.1 hP'.2).trans (hkernel P hP hPQ).symm

end AlgebraicGeometry
