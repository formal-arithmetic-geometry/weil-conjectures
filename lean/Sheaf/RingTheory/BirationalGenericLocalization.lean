/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Generic localization for a birational affine ring map

Source: Stacks Project, Morphisms, Tag 0BAB, lemma-birational-generic-fibres,
affine-ring paragraph; used in Tag 0BAC, lemma-birational-birational.
(blueprint: lem-sfb-birational-generic-localization)
-/

@[expose] public section

universe u v

namespace Localization

/-- If a ring map with unique minimal primes induces an isomorphism on their local rings,
it induces an isomorphism after localizing at the image of the base prime complement.

Source: Stacks Project, Morphisms, Tag 0BAB, lemma-birational-generic-fibres,
affine-ring paragraph (blueprint: lem-sfb-birational-generic-localization).

Proof:
1. Put S = B \ q, W = φ(S), C = W⁻¹A, and let λ : A → C be the localization map.
   The equality q = φ⁻¹(p) makes W disjoint from p. The fraction formulas define
   θ : B_q → C and ψ : C → A_p; their composite is the assumed isomorphism h.
   Well-definedness follows by applying φ, or the localization map, to the witness
   for equality of fractions (def-weil-pbc-localization-at-prime).
2. The localization prime correspondence
   (lem-weil-pbc-localization-prime-residue-field-iso, clause (1)) gives the prime
   J = pC with λ⁻¹(J) = p; it also gives contraction of pA_p equal to p.
3. Compose ψ with A_p → κ(p) to get ρ. Since ρθ is h followed by the residue quotient,
   ρ is surjective. A fraction a/w has zero residue exactly when a ∈ p, by step 2;
   the same criterion characterizes membership in J, so ker ρ = J. Thus J is maximal:
   for x outside J in an ideal I strictly containing J, lift ρ(x)⁻¹ to y in C;
   then 1 - xy ∈ J ⊆ I, so 1 ∈ I (def-weil-pbc-localization-at-prime).
4. For any prime P of C, its contraction Q is prime and P = QC by the same prime
   correspondence. Every prime of A contains a minimal prime
   (lem-weil-pbc-prime-contains-minimal-prime). Uniqueness gives p ⊆ Q, hence J ⊆ P.
5. Since J is maximal and every prime contains J, J is the only prime of C.
6. If t ∉ p, then λ(t) ∉ J by step 2 and λ(t) is a unit. Otherwise its proper
   principal ideal is contained in a maximal ideal
   (lem-weil-pbc-proper-ideal-contained-in-maximal). A maximal ideal is prime:
   if xy ∈ M and x ∉ M, write 1 = m + rx and multiply by y. Thus that maximal
   ideal equals J by step 5, a contradiction.
7. Define η : A_p → C by a/t ↦ λ(a)λ(t)⁻¹. An equality of fractions has a witness
   v ∉ p with v(at' - a't) = 0. Applying λ and cancelling units proves that η is
   well defined; the fraction operations show it is a ring map. On fractions,
   ψη and ηψ are identities (def-weil-pbc-localization-at-prime). Hence ψ is an
   isomorphism, and θ = ψ⁻¹h is an isomorphism. The conclusion states bijectivity
   of this specified ring homomorphism, rather than existence of an unrelated isomorphism.
-/
theorem bijective_map_of_unique_minimalPrimes
    {B : Type u} {A : Type v} [CommRing B] [CommRing A]
    (φ : B →+* A) (q : Ideal B) (p : Ideal A) [q.IsPrime] [p.IsPrime]
    (hB : minimalPrimes B = {q}) (hA : minimalPrimes A = {p})
    (hpq : q = p.comap φ)
    (h : Function.Bijective (Localization.localRingHom q p φ hpq)) :
    Function.Bijective
      (IsLocalization.map (S := Localization.AtPrime q)
        (Localization (q.primeCompl.map φ)) φ (Submonoid.le_comap_map q.primeCompl)) := by
  have hq : q ∈ minimalPrimes B := by
    rw [hB]
    exact Set.mem_singleton q
  have : q.IsPrime := hq.isPrime
  let W := q.primeCompl.map φ
  let C := Localization W
  have hW : W ≤ p.primeCompl := by
    rintro _ ⟨b, hb, rfl⟩
    change φ b ∉ p
    change b ∉ q at hb
    rw [hpq] at hb
    exact hb
  let θ : Localization.AtPrime q →+* C :=
    IsLocalization.map C φ (Submonoid.le_comap_map q.primeCompl)
  let ψ : C →+* Localization.AtPrime p :=
    IsLocalization.lift (M := W) (S := C)
      (g := algebraMap A (Localization.AtPrime p))
      (fun w ↦ IsLocalization.map_units (Localization.AtPrime p) ⟨(w : A), hW w.2⟩)
  have hcomp : ψ.comp θ = Localization.localRingHom q p φ hpq := by
    apply IsLocalization.ringHom_ext q.primeCompl
    ext b
    simp [ψ, θ]
  let ρ := (IsLocalRing.residue (Localization.AtPrime p)).comp ψ
  have hρ : Function.Surjective ρ := by
    have hs := (IsLocalRing.residue_surjective (R := Localization.AtPrime p)).comp h.2
    intro x
    obtain ⟨b, hb⟩ := hs x
    refine ⟨θ b, ?_⟩
    change IsLocalRing.residue _ ((ψ.comp θ) b) = x
    rw [hcomp]
    exact hb
  let J := RingHom.ker ρ
  have hJ : J.IsMaximal := by
    exact RingHom.ker_isMaximal_of_surjective ρ hρ
  have hJp : J.comap (algebraMap A C) = p := by
    ext a
    change IsLocalRing.residue _ (ψ (algebraMap A C a)) = 0 ↔ a ∈ p
    rw [show ψ (algebraMap A C a) = algebraMap A (Localization.AtPrime p) a by
      simp [ψ], IsLocalRing.residue_eq_zero_iff]
    change a ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime p)).under A ↔ a ∈ p
    rw [Localization.AtPrime.under_maximalIdeal]
  have hpJ : p.map (algebraMap A C) = J := by
    have : J.IsPrime := hJ.isPrime
    rw [← hJp]
    exact (IsLocalization.prime_localRing_residueField_iso A C W J).2.2.2.1
  have hprime : ∀ P : Ideal C, P.IsPrime → P = J := by
    intro P hP
    have : (P.comap (algebraMap A C)).IsPrime := Ideal.comap_isPrime _ P
    obtain ⟨r, hr, hrP⟩ := Ideal.exists_minimalPrimes_le
      (show (⊥ : Ideal A) ≤ P.comap (algebraMap A C) from bot_le)
    have hrp : r = p := by simpa only [hA, Set.mem_singleton_iff] using hr
    subst r
    apply (hJ.eq_of_le hP.ne_top ?_).symm
    rw [← hpJ, Ideal.map_le_iff_le_comap]
    exact hrP
  have hunits : ∀ t ∈ p.primeCompl, IsUnit (algebraMap A C t) := by
    intro t ht
    by_contra hu
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
      (Ideal.span {algebraMap A C t})
      (fun he ↦ hu (Ideal.span_singleton_eq_top.mp he))
    have hMJ := hprime M hM.isPrime
    have htM := hle (Ideal.subset_span (Set.mem_singleton _))
    rw [hMJ] at htM
    exact ht (show t ∈ p from hJp ▸ htM)
  have : IsLocalization p.primeCompl C := IsLocalization.of_le W p.primeCompl hW hunits
  let e := IsLocalization.algEquiv p.primeCompl C (Localization.AtPrime p)
  have hψ : ψ = e.toRingHom := by
    apply IsLocalization.ringHom_ext W
    ext a
    simp [ψ, e]
  have hθ : θ = e.symm.toRingHom.comp (Localization.localRingHom q p φ hpq) := by
    rw [← hcomp, hψ]
    ext x
    exact (e.symm_apply_apply (θ x)).symm
  change Function.Bijective θ
  rw [hθ]
  exact e.symm.bijective.comp h

end Localization
