/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.RegularLocalLiftRegularSequenceQuotient
import Sheaf.RingTheory.RegularSequencePrincipalNeighbourhood

/-!
# Openness of the regular locus from regular prime quotients

Source: Stacks Project, More on Algebra, Tag 07P9, lemma-intersection-regular-with-closed;
Tag 07P7, definition-J (blueprint: lem-exc-regular-locus-open-from-prime-quotients).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace RingTheory

private theorem regular_generalization
    (A : Type u) [CommRing A] (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (hqp : q ≤ p) [IsRegularLocalRing (Localization.AtPrime p)] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let e := IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime p) p
  let Q := e.symm ⟨q, inferInstance, hqp⟩
  have hQ : Q.1.IsPrime := Q.2
  have heq : Q.1.comap (algebraMap A (Localization.AtPrime p)) = q :=
    congrArg Subtype.val (e.apply_symm_apply ⟨q, inferInstance, hqp⟩)
  have := (IsRegularLocalRing.localization_at_prime_and_isRegularRing Q.1).1
  have hreg := IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      p.primeCompl Q.1).symm.toRingEquiv
  let E (r : PrimeSpectrum A) := IsRegularLocalRing (Localization.AtPrime r.asIdeal)
  have hs : (⟨Q.1.comap (algebraMap A (Localization.AtPrime p)), inferInstance⟩ :
      PrimeSpectrum A) = ⟨q, inferInstance⟩ := PrimeSpectrum.ext heq
  exact (congrArg E hs).mp hreg

private theorem span_range_mul_units {R : Type u} [CommRing R] {ι : Type}
    (f s : ι → R) (hs : ∀ i, IsUnit (s i)) :
    Ideal.span (Set.range (fun i ↦ s i * f i)) = Ideal.span (Set.range f) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    obtain ⟨s', hs'⟩ := hs i
    have hmem := Ideal.subset_span (s := Set.range (fun i ↦ s i * f i)) ⟨i, rfl⟩
    have h := Ideal.mul_mem_left _ (↑(s'⁻¹) : R) hmem
    simpa [← hs', ← mul_assoc] using h

private theorem exists_local_parameter_numerators
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] [IsRegularLocalRing (Localization.AtPrime p)]
    (d : ℕ) (hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞)) :
    ∃ f : Fin d → R, (∀ i, f i ∈ p) ∧
      Ideal.span (Set.range (fun i ↦ algebraMap R (Localization.AtPrime p) (f i))) =
        p.map (algebraMap R (Localization.AtPrime p)) := by
  classical
  let A := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal A
  have hrank : m.spanFinrank = d := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
    rw [hd] at h
    exact_mod_cast h
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (show (m : Submodule A A).FG from m.fg_of_isNoetherianRing)
  have hsd : s.card = d := hcard.trans hrank
  let g : Fin d → A := fun i ↦ (s.equivFinOfCardEq hsd).symm i
  have hgrange : Set.range g = (s : Set A) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((s.equivFinOfCardEq hsd).symm i).2
    · intro hx
      exact ⟨(s.equivFinOfCardEq hsd) ⟨x, hx⟩, by simp [g]⟩
  choose f t hft using fun i ↦ IsLocalization.exists_mk'_eq p.primeCompl (g i)
  have hmem (i : Fin d) : f i ∈ p := by
    apply (IsLocalization.AtPrime.mk'_mem_maximal_iff A p (f i) (t i)).mp
    rw [hft i]
    change g i ∈ m
    rw [← hspan]
    exact Submodule.subset_span (hgrange ▸ Set.mem_range_self i)
  refine ⟨f, hmem, ?_⟩
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  change Ideal.span (Set.range (fun i ↦ algebraMap R A (f i))) = m
  have heq (i : Fin d) : algebraMap R A (f i) = algebraMap R A (t i) * g i := by
    rw [← hft i, mul_comm]
    exact (IsLocalization.mk'_spec A (f i) (t i)).symm
  simp_rw [heq]
  rw [span_range_mul_units g (fun i ↦ algebraMap R A (t i))
    (fun i ↦ IsLocalization.map_units A (t i)), hgrange]
  exact hspan

private theorem parameters_principal
    (A : Type u) [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime p)] :
    ∃ (d : ℕ) (f : Fin d → A) (g : A), g ∉ p ∧ (∀ i, f i ∈ p) ∧
      Sequence.IsRegular (Localization.Away g)
        (List.ofFn (fun i ↦ algebraMap A (Localization.Away g) (f i))) ∧
      (Ideal.span (Set.range f)).map (algebraMap A (Localization.AtPrime p)) =
        p.map (algebraMap A (Localization.AtPrime p)) := by
  let d := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).spanFinrank
  have hd : ringKrullDim (Localization.AtPrime p) = (d : WithBot ℕ∞) :=
    IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  obtain ⟨f, hf, hspan⟩ := exists_local_parameter_numerators p d hd
  have hparameters : IsLocalRing.IsRegularSystemOfParameters
      (List.ofFn (fun i ↦ algebraMap A (Localization.AtPrime p) (f i))) := by
    refine ⟨?_, ?_⟩
    · simpa only [List.mem_ofFn', Set.ofPred_mem_eq] using
        hspan.trans (IsLocalization.AtPrime.map_eq_maximalIdeal p _)
    · simpa using hd.symm
  have hreg := (IsRegularLocalRing.isRegular_and_quotients_of_generators
    (Localization.AtPrime p) d hd _ hparameters).1
  obtain ⟨g, hg, hgreg⟩ :=
    exists_isRegular_localizationAway_of_isRegular_localizationAtPrime A p d f hreg
  refine ⟨d, f, g, hg, hf, hgreg, ?_⟩
  simpa only [Ideal.map_span, ← Set.range_comp'] using hspan

private theorem clear_prime_generators
    (A : Type u) [CommRing A] [IsNoetherianRing A] (p I : Ideal A) [p.IsPrime]
    (heq : I.map (algebraMap A (Localization.AtPrime p)) =
      p.map (algebraMap A (Localization.AtPrime p))) :
    ∃ s : A, s ∉ p ∧ ∀ a ∈ p, s * a ∈ I := by
  classical
  obtain ⟨t, ht⟩ := p.fg_of_isNoetherianRing
  have hden (a : t) : ∃ m : p.primeCompl, (m : A) * (a : A) ∈ I := by
    have ha : (a : A) ∈ p := ht ▸ Ideal.subset_span a.2
    have hm := Ideal.mem_map_of_mem (algebraMap A (Localization.AtPrime p)) ha
    rw [← heq] at hm
    obtain ⟨m, hm, hma⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
        (Localization.AtPrime p) I a).mp hm
    exact ⟨⟨m, hm⟩, hma⟩
  choose m hm using hden
  let s : p.primeCompl := ∏ a : t, m a
  refine ⟨s, s.2, ?_⟩
  have hle : (p : Submodule A A) ≤
      Submodule.comap (LinearMap.mul A A (s : A)) (I : Submodule A A) := by
    refine le_trans ht.symm.le ?_
    apply Submodule.span_le.mpr
    intro a ha
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (⟨a, ha⟩ : t))
    change (s : A) * a ∈ I
    have hs : (s : A) = (m ⟨a, ha⟩ : A) * (c : A) := congrArg Subtype.val hc
    rw [hs, mul_right_comm]
    exact I.mul_mem_right (c : A) (hm ⟨a, ha⟩)
  exact fun a ha ↦ hle ha

private theorem regularSequence_at_specialization
    (A : Type u) [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    (d : ℕ) (f : Fin d → A) (hf : ∀ i, f i ∈ p) (g : A)
    (hg : Sequence.IsRegular (Localization.Away g)
      (List.ofFn (fun i ↦ algebraMap A (Localization.Away g) (f i))))
    (q : Ideal A) [q.IsPrime] (hpq : p ≤ q) (hgq : g ∉ q) :
    Sequence.IsRegular (Localization.AtPrime q)
      (List.ofFn (fun i ↦ algebraMap A (Localization.AtPrime q) (f i))) := by
  let B := Localization.Away g
  let C := Localization.AtPrime q
  have hle : Submonoid.powers g ≤ q.primeCompl :=
    Submonoid.powers_le.mpr hgq
  let : Algebra B C :=
    IsLocalization.localizationAlgebraOfSubmonoidLe B C (Submonoid.powers g) q.primeCompl hle
  have : IsScalarTower A B C :=
    IsLocalization.localization_isScalarTower_of_submonoid_le B C
      (Submonoid.powers g) q.primeCompl hle
  have : IsLocalization (q.primeCompl.map (algebraMap A B)) C :=
    IsLocalization.isLocalization_of_submonoid_le B C
      (Submonoid.powers g) q.primeCompl hle
  have hw := hg.toIsWeaklyRegular.of_isLocalization C
    (q.primeCompl.map (algebraMap A B))
  have hw' : Sequence.IsWeaklyRegular C
      (List.ofFn (fun i ↦ algebraMap A C (f i))) := by
    rw [List.map_ofFn] at hw
    change Sequence.IsWeaklyRegular C
      (List.ofFn (fun i ↦ algebraMap B C (algebraMap A B (f i)))) at hw
    simpa only [← IsScalarTower.algebraMap_apply A B C] using hw
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr hw'
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff C q _).mpr (hpq (hf i))

private theorem quotient_regular_on_principal
    (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]
    (h : ∃ U : Set (PrimeSpectrum (A ⧸ p)), IsOpen U ∧ U.Nonempty ∧
      ∀ q : PrimeSpectrum (A ⧸ p), q ∈ U →
        IsRegularLocalRing (Localization.AtPrime q.asIdeal)) :
    ∃ b : A, b ∉ p ∧ ∀ (q : Ideal A) [q.IsPrime], p ≤ q → b ∉ q →
      IsRegularLocalRing (Localization.AtPrime q ⧸ p.map
        (algebraMap A (Localization.AtPrime q))) := by
  obtain ⟨U, hU, ⟨x, hx⟩, hreg⟩ := h
  obtain ⟨_, ⟨bbar, rfl⟩, hxb, hbU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hU
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective bbar
  have hbp : b ∉ p := by
    intro hbp
    apply hxb
    change Ideal.Quotient.mk p b ∈ x.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hbp]
    exact x.asIdeal.zero_mem
  refine ⟨b, hbp, ?_⟩
  intro q hq hpq hbq
  let qbar := q.map (Ideal.Quotient.mk p)
  have : qbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have hc : qbar.comap (Ideal.Quotient.mk p) = q := by
    dsimp [qbar]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hpq]
  have hqbar : (⟨qbar, inferInstance⟩ : PrimeSpectrum (A ⧸ p)) ∈ U := by
    apply hbU
    change Ideal.Quotient.mk p b ∉ qbar
    intro hm
    exact hbq (hc ▸ hm)
  have : IsRegularLocalRing (Localization.AtPrime qbar) := hreg _ hqbar
  have hM : Algebra.algebraMapSubmonoid (A ⧸ p) q.primeCompl = qbar.primeCompl := by
    simpa only [Algebra.algebraMapSubmonoid, Ideal.Quotient.algebraMap_eq, hc] using
      qbar.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective
  have : IsLocalization qbar.primeCompl
      (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q))) := by
    rw [← hM]
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv qbar.primeCompl (Localization.AtPrime qbar)
      (Localization.AtPrime q ⧸ p.map (algebraMap A (Localization.AtPrime q)))).toRingEquiv

private theorem regular_specialization_neighbourhood
    (A : Type u) [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime p)]
    (h : ∃ U : Set (PrimeSpectrum (A ⧸ p)), IsOpen U ∧ U.Nonempty ∧
      ∀ q : PrimeSpectrum (A ⧸ p), q ∈ U →
        IsRegularLocalRing (Localization.AtPrime q.asIdeal)) :
    ∃ k ∉ p, ∀ (q : Ideal A) [q.IsPrime], p ≤ q → k ∉ q →
      IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨d, f, g, hgp, hf, hreg, hspan⟩ := parameters_principal A p
  let I := Ideal.span (Set.range f)
  obtain ⟨s, hsp, hs⟩ := clear_prime_generators A p I hspan
  obtain ⟨b, hbp, hb⟩ := quotient_regular_on_principal A p h
  refine ⟨g * s * b, p.primeCompl.mul_mem (p.primeCompl.mul_mem hgp hsp) hbp, ?_⟩
  intro q hq hpq hkq
  have hgsq : g * s ∉ q := fun hm ↦ hkq (q.mul_mem_right b hm)
  have hgq : g ∉ q := fun hm ↦ hgsq (q.mul_mem_right s hm)
  have hsq : s ∉ q := fun hm ↦ hgsq (q.mul_mem_left g hm)
  have hbq : b ∉ q := fun hm ↦ hkq (q.mul_mem_left (g * s) hm)
  let C := Localization.AtPrime q
  have heq : I.map (algebraMap A C) = p.map (algebraMap A C) := by
    apply le_antisymm
    · apply Ideal.map_mono
      exact Ideal.span_le.mpr (by rintro x ⟨i, rfl⟩; exact hf i)
    · apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      change algebraMap A C a ∈ I.map (algebraMap A C)
      apply (Ideal.unit_mul_mem_iff_mem _
        (IsLocalization.map_units C (⟨s, hsq⟩ : q.primeCompl))).mp
      rw [← map_mul]
      exact Ideal.mem_map_of_mem _ (hs a ha)
  let xs := List.ofFn (fun i ↦ algebraMap A C (f i))
  have hxs : Ideal.ofList xs = p.map (algebraMap A C) := by
    rw [← heq]
    dsimp [I, xs, Ideal.ofList]
    rw [Ideal.map_span]
    congr 1
    ext x
    simp
  have hquot : IsRegularLocalRing (C ⧸ p.map (algebraMap A C)) := hb q hpq hbq
  have : IsRegularLocalRing (C ⧸ Ideal.ofList xs) := by
    rw [hxs]
    exact hquot
  apply isRegularLocalRing_of_regularSequence_quotient C xs
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff C q _).mpr (hpq (hf i))
  · exact regularSequence_at_specialization A p d f hf g hreg q hpq hgq

/-- A Noetherian ring has open regular locus if each prime quotient has a nonempty regular open.

Source: Stacks Project, More on Algebra, Tag 07P9, lemma-intersection-regular-with-closed;
Tag 07P7, definition-J (blueprint: lem-exc-regular-locus-open-from-prime-quotients).

Proof (the seven steps of the node):
1. Put `E = {p | A_p is regular local}`. If `q ⊆ p` and `p ∈ E`, view `q A_p` as a
   prime of `A_p` using `lem-weil-pbc-primes-of-localization`. Its localization is regular
   by `lem-weil-pbc-regular-local-localization`, and is `A_q` by
   `lem-weil-pbc-localize-localization-at-prime`. Thus `E` is stable under generalization.
2. At `p ∈ E`, choose `r = dim A_p` generators of its maximal ideal
   (`def-weil-regular-scheme`). Write them as `a_i/s_i` with `a_i ∈ p`, `s_i ∉ p`.
   Since the denominators are units, the numerators still generate. They form a regular
   sequence in `A_p` by `lem-weil-pbc-regular-local-generators-regular-sequence`, also
   when `r = 0`.
3. By `lem-exc-regular-sequence-principal-neighbourhood`, there is `g ∉ p` on whose
   principal open these numerators form a regular sequence.
4. Write `p = (a_1,...,a_m)` by Noetherianity. Express each `a_j/1` in terms of the
   chosen numerators in `A_p`, clear its finitely many denominators, and multiply by an
   element outside `p` witnessing equality of fractions. This yields `s_j ∉ p` with
   `s_j a_j` in the ideal `I` of the numerators. Put `h = g ∏ s_j`. In `B = A[1/h]`,
   `p B = I B`. Localization preserves regularity: apply
   `lem-weil-pbc-localization-module-exact` to multiplication on each successive quotient
   and identify its localization with the corresponding quotient of `B`. Explicitly,
   `(c + J)/s^n` maps to `c/s^n + J B`; clearing powers of `s` proves its kernel zero
   and surjectivity is immediate from fractions. The final quotient is nonzero because
   `I B ⊆ p B`, and `h ∉ p` makes `p B` proper. This is
   `def-weil-pbc-regular-sequence`.
5. The complement of the assumed open in `Spec (A/p)` is `V(J)` by
   `lem-weil-pbc-spec-irreducible-closed-subsets-primes`. Nonemptiness gives `J ≠ 0`.
   Choose a nonzero element of `J`, lift it to `b ∉ p`, and put `k = h b ∉ p`.
   For every `q ⊇ p` avoiding `k`, its quotient prime lies in that regular open, and
   `h ∉ q`.
6. Localize the regular sequence in `B` at such a `q`, using
   `lem-weil-pbc-weakly-regular-sequence-localization-prime` and the canonical fraction
   identification with `A_q`. Its generated ideal is `p A_q`, whose quotient is the
   regular local ring `(A/p)_(q/p)` by `lem-weil-pbc-localization-at-prime-of-quotient`.
   Since `A_q` is Noetherian by `lem-weil-pbc-localization-noetherian`, apply
   `lem-exc-regular-local-lift-regular-sequence-quotient` to conclude `q ∈ E`.
7. Steps 1 and 2--6 give the two hypotheses of
   `lem-exc-nagata-principal-open-criterion`. Hence every point of `E` lies in a principal
   open contained in `E`. Their union is `E`, so `E` is open. For the zero ring both
   the spectrum and this union are empty.
-/
theorem isOpen_regularLocus_of_primeQuotient_regularOpen
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (h : ∀ (p : Ideal A), p.IsPrime →
      ∃ U : Set (PrimeSpectrum (A ⧸ p)),
        IsOpen U ∧ U.Nonempty ∧
          ∀ q : PrimeSpectrum (A ⧸ p), q ∈ U →
            IsRegularLocalRing (Localization.AtPrime q.asIdeal)) :
    IsOpen {q : PrimeSpectrum A |
      IsRegularLocalRing (Localization.AtPrime q.asIdeal)} := by
  let E : Ideal A → Prop := fun p ↦
    ∃ _ : p.IsPrime, IsRegularLocalRing (Localization.AtPrime p)
  have hgen : ∀ p q : Ideal A, p.IsPrime → q.IsPrime → q ≤ p → E p → E q := by
    intro p q hp hq hqp ⟨_, hreg⟩
    exact ⟨hq, regular_generalization A p q hqp⟩
  have hloc : ∀ p : Ideal A, p.IsPrime → E p →
      ∃ g ∉ p, ∀ q : Ideal A, q.IsPrime → p ≤ q → g ∉ q → E q := by
    intro p hp ⟨_, hreg⟩
    obtain ⟨g, hgp, hg⟩ := regular_specialization_neighbourhood A p (h p hp)
    exact ⟨g, hgp, fun q hq hpq hgq ↦ ⟨hq, hg q hpq hgq⟩⟩
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  obtain ⟨g, hgp, hg⟩ :=
    Ideal.exists_notMem_forall_of_isNoetherianRing E hgen hloc p.asIdeal ⟨p.isPrime, hp⟩
  exact Filter.mem_of_superset
    (PrimeSpectrum.isOpen_basicOpen.mem_nhds hgp) (fun q hq ↦ (hg q.asIdeal q.isPrime hq).2)

end RingTheory
