/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Topology.Connected.Separation

/-!
# Zero-dimensional affine spectra are profinite

Source: Stacks Project, Tag 04MG, `lemma-ring-with-only-minimal-primes`, implication
(6) to (1), (2), (3) (blueprint: lem-weil-pbc-zero-dimensional-spectrum-profinite).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- If every prime ideal is maximal, the Zariski spectrum is compact, Hausdorff and totally
 disconnected. Source: Stacks Project, Tag 04MG, `lemma-ring-with-only-minimal-primes`
 (blueprint: lem-weil-pbc-zero-dimensional-spectrum-profinite).

Proof plan:
1. Every prime is minimal: a prime contained in it is maximal, so the inclusion is equality.
2. For `g ∈ p`, the radical-localization theorem
   (`lem-weil-pbc-minimal-prime-localization-radical`) applied to the zero ideal says `g/1`
   is nilpotent in `A_p`. The fraction relation of `def-weil-pbc-localization-at-prime`
   gives `s ∉ p` and a positive `n` with `s * g^n = 0`.
3. Consequently `D(s)` contains `p` and misses `D(g)`. The complement of each `D(g)`
   is open, so every standard open is clopen.
4. Distinct primes are separated by a standard open and its complement. These are
   disjoint open neighbourhoods, proving Hausdorffness. The same clopen separation
   prevents any connected subset from containing two distinct points, proving total
   disconnectedness.
5. `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`, clause (iii), supplies
   compactness for every commutative ring. These three properties mean profiniteness.
   The argument also includes the zero ring, whose spectrum is empty. -/
theorem Spec.profinite_of_isMaximal (A : Type u) [CommRing A]
    (h : ∀ p : Ideal A, p.IsPrime → p.IsMaximal) :
    CompactSpace (Spec (CommRingCat.of A)) ∧
      T2Space (Spec (CommRingCat.of A)) ∧
      TotallyDisconnectedSpace (Spec (CommRingCat.of A)) := by
  classical
  change CompactSpace (PrimeSpectrum A) ∧ T2Space (PrimeSpectrum A) ∧
    TotallyDisconnectedSpace (PrimeSpectrum A)
  have hclopen (g : A) : IsClopen (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) := by
    refine ⟨?_, (PrimeSpectrum.basicOpen g).isOpen⟩
    rw [← isOpen_compl_iff]
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hgp : g ∈ p.asIdeal := by
      simpa only [Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
        not_not] using hp
    have hmin : p.asIdeal ∈ (⊥ : Ideal A).minimalPrimes := by
      refine ⟨⟨p.isPrime, bot_le⟩, ?_⟩
      intro q hq hqp
      exact le_of_eq ((h q hq.1).eq_of_le p.isPrime.ne_top hqp).symm
    let L := Localization.AtPrime p.asIdeal
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      (A := L) p.asIdeal (⊥ : Ideal A) hmin
    have hnil : algebraMap A L g ∈ (⊥ : Ideal L).radical := by
      rw [← Ideal.map_bot (f := algebraMap A L), hrad]
      exact Ideal.mem_map_of_mem _ hgp
    obtain ⟨n, hn⟩ := hnil
    have heq : algebraMap A L (g ^ n) = 0 := by
      simpa only [map_pow, Ideal.mem_bot] using hn
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl L (g ^ n)).mp heq
    refine Filter.mem_of_superset ((PrimeSpectrum.basicOpen s.val).isOpen.mem_nhds s.property) ?_
    intro q hqs
    change ¬ g ∉ q.asIdeal
    intro hgq
    rcases q.isPrime.mem_or_mem_of_mul_eq_zero hs with hsq | hgn
    · exact hqs hsq
    · exact hgq (q.isPrime.mem_of_pow_mem n hgn)
  have hsep : TotallySeparatedSpace (PrimeSpectrum A) := by
    apply totallySeparatedSpace_iff_exists_isClopen.mpr
    intro p q hpq
    have hnot : ¬ q.asIdeal ≤ p.asIdeal := by
      intro hqp
      exact hpq (PrimeSpectrum.ext ((h q.asIdeal q.isPrime).eq_of_le
        p.isPrime.ne_top hqp).symm)
    obtain ⟨g, hgq, hgp⟩ := SetLike.not_le_iff_exists.mp hnot
    exact ⟨PrimeSpectrum.basicOpen g, hclopen g, hgp, by
      simpa only [Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
        not_not] using hgq⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry
