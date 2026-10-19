/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!+# A parameter identifying a local curve's principal localization with its total fractions

Source: Stacks Project, Varieties, Tag 0C3R, Lemma 33.39.1, existence and condition (5)
for a reduced ring (blueprint: lem-exc-local-curve-principal-total-fractions).
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A reduced Noetherian local ring of dimension one has a regular parameter whose
canonical map from the principal localization to the total fraction ring is an isomorphism.
Source: Stacks Project, Tag 0C3R, existence and condition (5)
(blueprint: lem-exc-local-curve-principal-total-fractions).

Proof:
1. Apply `lem-weil-pbc-noetherian-local-system-of-parameters` in dimension one to choose
   `f` in the maximal ideal with the radical of `(f)` equal to the maximal ideal.
2. Every prime lies in the maximal ideal by `lem-weil-pbc-local-ring-unit-criterion`.
   Dimension one rules out a chain of three distinct primes. Hence every other prime
   is minimal, and the maximal ideal is not minimal. A minimal prime containing `f`
   would contain the radical of `(f)`, so would equal the maximal ideal. Thus none does.
3. By `lem-weil-pbc-reduced-zerodivisors-union-minimal-primes`, `f` is a nonzerodivisor.
   Nonzerodivisors form a multiplicative set, containing every power of `f`.
4. The universal property of localization gives the canonical algebra map, sending
   `r / f^n` to the same fraction in the total ring of fractions. Its fraction formula
   is well defined by the equality criterion of `def-weil-pbc-module-localization`
   and `def-weil-ring-localization-away`.
5. Every nonzerodivisor `s` divides some power of `f`: for a unit use the zeroth power;
   otherwise `s` lies in the maximal ideal and in no minimal prime, so that ideal is
   the only prime containing `(s)`. The radical-intersection clause of
   `lem-weil-pbc-zero-locus-eq-iff-radical-eq` gives `radical (s) = maximalIdeal R`.
   Thus `f^n = s * a` for some positive `n` and some `a`.
6. The canonical map is injective: a fraction mapping to zero has numerator killed
   by a nonzerodivisor, hence zero. It is surjective: writing `f^n = s * a` as in
   step 5, the total fraction `r / s` is the image of `(r * a) / f^n`. A bijective
   algebra homomorphism is an algebra isomorphism, proving all clauses for this `f`.
-/
theorem exists_parameter_principal_total_fractions
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsReduced R]
    (hdim : ringKrullDim R = 1) :
    ∃ (f : R) (hf : f ∈ nonZeroDivisors R),
      f ∈ maximalIdeal R ∧
      (∀ p ∈ minimalPrimes R, f ∉ p) ∧
      (Ideal.span ({f} : Set R)).radical = maximalIdeal R ∧
      Function.Bijective
        (IsLocalization.Away.liftAlgHom (S := Localization.Away f)
          (f := Algebra.ofId R (FractionRing R)) f
          (IsLocalization.map_units (FractionRing R) ⟨f, hf⟩)) := by
  classical
  have hmheight : (maximalIdeal R).height = 1 := by
    have h := maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hdim] at h
    exact WithBot.coe_injective h
  have hprime (p : Ideal R) [p.IsPrime] (hne : p ≠ maximalIdeal R) :
      p ∈ minimalPrimes R := by
    rw [← Ideal.height_eq_zero_iff]
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime
      (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hne)
    rw [hmheight, Order.lt_one_iff] at hlt
    exact hlt
  have hmnot : maximalIdeal R ∉ minimalPrimes R := by
    rw [← Ideal.height_eq_zero_iff, hmheight]
    exact one_ne_zero
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal R)
  have hcard' : s.card = 1 := by
    rw [hmheight] at hcard
    exact_mod_cast hcard
  obtain ⟨f, rfl⟩ := Finset.card_eq_one.mp hcard'
  simp only [Finset.coe_singleton] at hs
  have hfmem : f ∈ maximalIdeal R := hs.le (Ideal.subset_span (by simp))
  have hrad : (Ideal.span ({f} : Set R)).radical = maximalIdeal R := by
    rw [Ideal.radical_eq_sInf]
    apply le_antisymm
    · exact sInf_le ⟨hs.le, inferInstance⟩
    · refine le_sInf fun p ⟨hsp, hp⟩ ↦ ?_
      have := hp
      exact hs.2 ⟨hp, hsp⟩ (le_maximalIdeal hp.ne_top)
  have hfavoid : ∀ p ∈ minimalPrimes R, f ∉ p := by
    intro p hp hfp
    have := hp.isPrime
    have hle : maximalIdeal R ≤ p := by
      rw [← hrad]
      exact hp.isPrime.radical_le_iff.mpr ((Ideal.span_singleton_le_iff_mem p).mpr hfp)
    have heq := le_antisymm hle (le_maximalIdeal hp.isPrime.ne_top)
    exact hmnot (heq.symm ▸ hp)
  have hfreg : f ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    by_contra hane
    have hfm : f ∈ ⋃ p ∈ (⊥ : Ideal R).minimalPrimes, (p : Set R) := by
      rw [Ideal.iUnion_minimalPrimes]
      exact ⟨a, by simpa using hane, by simpa [mul_comm] using ha⟩
    have hex : ∃ p ∈ minimalPrimes R, f ∈ p := by
      simpa only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] using hfm
    obtain ⟨p, hp, hfp⟩ := hex
    exact hfavoid p hp hfp
  refine ⟨f, hfreg, hfmem, hfavoid, hrad, ?_⟩
  have hden (s : R) (hs : s ∈ nonZeroDivisors R) : ∃ n : ℕ, s ∣ f ^ n := by
    have hfrad : f ∈ (Ideal.span ({s} : Set R)).radical := by
      rw [Ideal.radical_eq_sInf]
      refine Ideal.mem_sInf.mpr fun p ⟨hsp, hp⟩ ↦ ?_
      have := hp
      by_cases heq : p = maximalIdeal R
      · simpa [heq] using hfmem
      · have hpmin := hprime p heq
        exact False.elim
          (notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
            (hsp (Ideal.subset_span (Set.mem_singleton s))) hpmin hs)
    obtain ⟨n, hn⟩ := hfrad
    exact ⟨n, Ideal.mem_span_singleton.mp hn⟩
  let : IsLocalization (nonZeroDivisors R) (Localization.Away f) :=
    IsLocalization.of_le_of_exists_dvd (Submonoid.powers f) (nonZeroDivisors R)
      (Submonoid.powers_le.mpr hfreg) (fun s hs ↦ by
        obtain ⟨n, hn⟩ := hden s hs
        exact ⟨f ^ n, ⟨n, rfl⟩, hn⟩)
  apply IsLocalization.bijective (nonZeroDivisors R)
    (IsLocalization.Away.liftAlgHom (S := Localization.Away f)
      (f := Algebra.ofId R (FractionRing R)) f
      (IsLocalization.map_units (FractionRing R) ⟨f, hfreg⟩)).toRingHom
  ext r
  exact (IsLocalization.Away.liftAlgHom (S := Localization.Away f)
    (f := Algebra.ofId R (FractionRing R)) f
    (IsLocalization.map_units (FractionRing R) ⟨f, hfreg⟩)).commutes r

end IsLocalRing
