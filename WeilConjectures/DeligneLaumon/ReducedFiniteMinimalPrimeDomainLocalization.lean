/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Domain after removing the other minimal components

Source: Stacks Project, `more-algebra.tex`, Tag 0GSC, the principal-localization
argument in `lemma-local-unramified-extension-unibranch-domain-is-etale` (blueprint:
`lem-dl-a1-reduced-finite-minimal-prime-domain-localization`).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- A reduced commutative ring with finitely many minimal primes becomes a domain after
localizing away from a prime containing exactly one minimal prime.

Source: Stacks Project, `more-algebra.tex`, Tag 0GSC, proof, the paragraph choosing an
 element outside the marked prime and in all other minimal primes and then localizing
 (blueprint: `lem-dl-a1-reduced-finite-minimal-prime-domain-localization`). The conclusion
uses the principal localization `Localization.Away`, corresponding to
`def-weil-ring-localization-away`.

Proof (as formalized below):
1. Enumerate the finite set of minimal primes, with the unique member contained in `Q` first.
   Choose an element outside `Q` from each other minimal prime and multiply them; primality
   of `Q` keeps the product outside `Q`, while it lies in every other minimal prime.
2. The principal-localization prime correspondence
   (`lem-dl-a1-principal-localization-prime-correspondence`) removes exactly those other minimal
   primes, so the localization has the one surviving
   minimal prime.
3. Localization preserves reducedness (`lem-dl-a1-localization-preserves-reduced`), and
   `lem-per-nilradical-minimal-prime-intersection` identifies the intersection of minimal
   primes with the nilradical. Thus the unique minimal prime is zero, and the localization
   is a domain; `def-weil-ring-localization-away` identifies it with `C[1/h]`.
-/
theorem exists_away_domain_of_reduced_of_finite_minimalPrimes
    (C : Type u) [CommRing C] [IsReduced C]
    (hfinite : (minimalPrimes C).Finite)
    (Q : Ideal C) [Q.IsPrime]
    (hunique : ∃! P : Ideal C, P ∈ minimalPrimes C ∧ P ≤ Q) :
    ∃ h : C, h ∉ Q ∧ IsDomain (Localization.Away h) := by
  classical
  obtain ⟨P₀, ⟨hP₀min, hP₀Q⟩, huniq⟩ := hunique
  let s : Finset (Ideal C) := hfinite.toFinset
  let t : Finset (Ideal C) := s.erase P₀
  have hmem_s (P : Ideal C) : P ∈ s ↔ P ∈ minimalPrimes C := by
    simp [s]
  have hmem_t (P : Ideal C) (hP : P ∈ t) : P ∈ minimalPrimes C := by
    exact (hmem_s P).mp ((Finset.mem_erase.mp hP).2)
  have hne_P₀ (P : Ideal C) (hP : P ∈ t) : P ≠ P₀ :=
    (Finset.mem_erase.mp hP).1
  have hnotle (P : Ideal C) (hP : P ∈ t) : ¬ P ≤ Q := by
    intro hPQ
    exact hne_P₀ P hP (huniq P ⟨hmem_t P hP, hPQ⟩)
  let x : Ideal C → C := fun P ↦
    if hP : P ∈ t then Classical.choose (Set.not_subset.mp (hnotle P hP)) else 1
  have hx_mem (P : Ideal C) (hP : P ∈ t) : x P ∈ P := by
    simp only [x, dif_pos hP]
    exact (Classical.choose_spec (Set.not_subset.mp (hnotle P hP))).1
  have hx_not (P : Ideal C) (hP : P ∈ t) : x P ∉ Q := by
    simp only [x, dif_pos hP]
    exact (Classical.choose_spec (Set.not_subset.mp (hnotle P hP))).2
  let h : C := (∏ P ∈ t, x P)
  have hh_not : h ∉ Q := by
    rw [show h = (∏ P ∈ t, x P) by rfl, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨P, hP, hxQ⟩
    exact (hx_not P hP) hxQ
  have hmem_prod (P : Ideal C) (hP : P ∈ t) : h ∈ P := by
    dsimp [h]
    rw [← Finset.mul_prod_erase t x hP]
    exact P.mul_mem_right _ (hx_mem P hP)
  let S := Localization.Away h
  let ι : C →+* S := algebraMap C S
  have hP₀_not : h ∉ P₀ := by
    intro hh
    exact hh_not (hP₀Q hh)
  have hP₀_disj : Disjoint (Submonoid.powers h : Set C) (P₀ : Set C) := by
    rw [Set.disjoint_left]
    rintro z ⟨n, rfl⟩ hp
    exact hP₀_not (hP₀min.isPrime.mem_of_pow_mem n hp)
  have hM₀prime : (Ideal.map ι P₀).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers h) S P₀
      hP₀min.isPrime hP₀_disj
  have hmap := IsLocalization.minimalPrimes_map (Submonoid.powers h) S (⊥ : Ideal C)
  have hM₀min' : Ideal.map (algebraMap C S) P₀ ∈
      ((⊥ : Ideal C).map (algebraMap C S)).minimalPrimes := by
    rw [hmap]
    change Ideal.under C (Ideal.map (algebraMap C S) P₀) ∈ minimalPrimes C
    rw [IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers h) S
      hP₀min.isPrime hP₀_disj]
    exact hP₀min
  have hM₀min : Ideal.map ι P₀ ∈ minimalPrimes S := by
    simpa [ι] using hM₀min'
  have hmin_eq (M : Ideal S) (hM : M ∈ minimalPrimes S) : M = Ideal.map ι P₀ := by
    have hMprime : M.IsPrime := hM.isPrime
    have hMmem : M ∈ ((⊥ : Ideal C).map ι).minimalPrimes := by
      simpa using hM
    have hMunder : M.under C ∈ minimalPrimes C := by
      rw [hmap] at hMmem
      exact hMmem
    have hMdisj : Disjoint (Submonoid.powers h : Set C) (M.under C : Set C) :=
      (IsLocalization.isPrime_iff_isPrime_disjoint (Submonoid.powers h) S M).mp
        hMprime |>.2
    have hhM : h ∉ M.under C := by
      intro hh
      have hpows : h ∈ (Submonoid.powers h : Set C) := by
        exact ⟨1, by simp⟩
      exact Set.disjoint_left.mp hMdisj hpows hh
    have heq : M.under C = P₀ := by
      by_contra hne
      have hPt : M.under C ∈ t :=
        Finset.mem_erase.mpr ⟨hne, (hmem_s _).mpr hMunder⟩
      exact hhM (hmem_prod (M.under C) hPt)
    calc
      M = Ideal.map ι (M.under C) := (IsLocalization.map_under (Submonoid.powers h) S M).symm
      _ = Ideal.map ι P₀ := congrArg (Ideal.map ι) heq
  have hsinf : sInf (minimalPrimes S) = (⊥ : Ideal S) := by
    rw [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced]
  have hsinf_eq : sInf (minimalPrimes S) = Ideal.map ι P₀ := by
    apply le_antisymm
    · exact sInf_le hM₀min
    · refine le_sInf fun M hM ↦ ?_
      rw [hmin_eq M hM]
  have hbot : (⊥ : Ideal S).IsPrime := by
    rw [← hsinf, hsinf_eq]
    exact hM₀prime
  refine ⟨h, hh_not, ?_⟩
  exact IsDomain.of_bot_isPrime S

end
