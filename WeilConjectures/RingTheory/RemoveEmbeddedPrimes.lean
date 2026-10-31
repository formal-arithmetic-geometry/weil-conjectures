/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.GDelta.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

/-!
# Removing embedded associated primes

Source: Stacks Project, Tag 02M6, `algebra-lemma-remove-embedded-primes`
(blueprint: lem-sc-hilbert-embedded-points-affine-removal).
-/

@[expose] public section

universe u v

namespace Module

private theorem nowhereDense_iff_avoids_generics {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] {S : Set X} (hS : IsClosed S) :
    IsNowhereDense S ↔ ∀ x ∈ genericPoints X, x ∉ S := by
  rw [hS.isNowhereDense_iff]
  constructor
  · intro h x hx hxS
    obtain ⟨U, hU, ⟨y, hy⟩, hUZ⟩ :=
      TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hx
    have hZS : closure ({x} : Set X) ⊆ S :=
      hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxS)
    have : y ∈ interior S := interior_maximal (hUZ.trans hZS) hU hy
    simp [h] at this
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨y, hy, hyU⟩ :=
      (closure_inter_open_nonempty_iff isOpen_interior).mp
        (show (closure (genericPoints X) ∩ interior S).Nonempty from
          ⟨x, by rw [genericPoints.closure]; trivial, hx⟩)
    exact h y hy (interior_subset hyU)

private theorem support_closure_singleton
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (p q : support R M) :
    q ∈ closure ({p} : Set (support R M)) ↔ p.val ≤ q.val := by
  rw [← specializes_iff_mem_closure, subtype_specializes_iff,
    ← PrimeSpectrum.le_iff_specializes]

private theorem support_generic_iff_minimal
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : support R M) :
    p ∈ genericPoints (support R M) ↔
      Minimal (fun q : PrimeSpectrum R ↦ q ∈ support R M) p.val := by
  have : QuasiSober (support R M) :=
    (isClosed_support (R := R) (M := M)).isClosedEmbedding_subtypeVal.quasiSober
  constructor
  · intro hp
    refine ⟨p.property, fun q hq hqp ↦ ?_⟩
    have hsub : closure ({p} : Set (support R M)) ⊆ closure ({⟨q, hq⟩} : Set _) := by
      intro r hr
      exact (support_closure_singleton _ _).mpr
        (hqp.trans ((support_closure_singleton _ _).mp hr))
    have heq := hp.2 isIrreducible_singleton.closure hsub
    exact (support_closure_singleton p ⟨q, hq⟩).mp
      (heq (subset_closure (Set.mem_singleton _)))
  · intro hp
    refine ⟨isIrreducible_singleton.closure, fun Z hZ hsub ↦ ?_⟩
    let y := hZ.genericPoint
    have hy : IsGenericPoint y (closure Z) := hZ.isGenericPoint_genericPoint_closure
    have hpy : p ∈ closure Z := subset_closure (hsub (subset_closure (by simp)))
    have hyp : y.val ≤ p.val := (support_closure_singleton y p).mp (hy ▸ hpy)
    have hle := hp.2 y.property hyp
    intro z hz
    exact (support_closure_singleton p z).mpr
      (hle.trans ((support_closure_singleton y z).mp (hy ▸ subset_closure hz)))

private theorem minimal_support_iff
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : PrimeSpectrum R) :
    Minimal (fun q : PrimeSpectrum R ↦ q ∈ support R M) p ↔
      p.asIdeal ∈ (annihilator R M).minimalPrimes := by
  simp only [Minimal, mem_support_iff_of_finite, Ideal.minimalPrimes, Ideal.IsMinimalPrime]
  constructor
  · rintro ⟨hp, hmin⟩
    exact ⟨⟨p.isPrime, hp⟩, fun q hq hqp ↦ hmin hq.2 (show (⟨q, hq.1⟩ : PrimeSpectrum R) ≤ p
      from hqp)⟩
  · rintro ⟨hp, hmin⟩
    exact ⟨hp.2, fun q hq hqp ↦ hmin ⟨q.isPrime, hq⟩ hqp⟩

private theorem nowhereDense_support_iff
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (K : Submodule R M) :
    IsNowhereDense {p : support R M | p.val ∈ support R K} ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ∈ (annihilator R M).minimalPrimes →
        p ∉ support R K := by
  have : QuasiSober (support R M) :=
    (isClosed_support (R := R) (M := M)).isClosedEmbedding_subtypeVal.quasiSober
  have hs : IsClosed {p : support R M | p.val ∈ support R K} :=
    (isClosed_support (R := R) (M := K)).preimage continuous_subtype_val
  rw [nowhereDense_iff_avoids_generics hs]
  constructor
  · intro h p hp
    have hp' := (minimal_support_iff p).mpr hp
    exact h ⟨p, hp'.1⟩ ((support_generic_iff_minimal _).mpr hp')
  · intro h p hp
    exact h p.val ((minimal_support_iff _).mp ((support_generic_iff_minimal _).mp hp))

private theorem associated_mem_support
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈ support R M := by
  obtain ⟨_, x, hx⟩ := isAssociatedPrime_iff.mp hp
  apply mem_support_iff_exists_annihilator.mpr
  exact ⟨x, by rw [← Submodule.bot_colon', ← hx]⟩

private theorem minimal_associated_iff
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) (hp : p ∈ associatedPrimes R M) :
    Minimal (fun q : Ideal R ↦ q ∈ associatedPrimes R M) p ↔
      p ∈ (annihilator R M).minimalPrimes := by
  have := hp.isPrime
  constructor
  · intro h
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
      (annihilator_le_of_mem_support (associated_mem_support p hp))
    have hqa := associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq
    exact (h.eq_of_le hqa hqp) ▸ hq
  · intro h
    refine ⟨hp, fun q hq hqp ↦ ?_⟩
    exact h.2 ⟨hq.isPrime, annihilator_le_of_mem_support (associated_mem_support q hq)⟩ hqp

/-- A finite module over a Noetherian commutative ring has a maximal submodule with
nowhere dense support in its own support. The quotient has the same support and no
embedded associated primes, and the localized quotient map is an isomorphism away from
any element belonging to every embedded associated prime of the original module.
`IsNowhereDense` is evaluated in the subspace `Module.support R M`.
Under the Noetherian hypothesis, `isAssociatedPrime_iff` identifies Mathlib's associated
primes with the annihilators of elements, as required here.

Source: Stacks Project, Tag 02M6, `algebra-lemma-remove-embedded-primes`
(blueprint: lem-sc-hilbert-embedded-points-affine-removal).

Proof following Stacks Tag 02M6, with K constructed as the intersection of the kernels
of localization at the minimal support primes:
1. The generic points of the closed Noetherian support are precisely its minimal
   primes. A closed subset is nowhere dense exactly when it avoids these generic points.
2. K vanishes at every such prime. Any nowhere-dense-support submodule also vanishes
   there, so it is contained in K. Thus K is the greatest such submodule.
3. The support exact sequence shows that the quotient retains every minimal support
   prime and hence the entire support. A lift of a nonzero quotient element survives
   at some minimal prime. If the element has prime annihilator q, then q is contained
   in this minimal prime, so equality follows and q is minimal.
4. Every minimal support prime of K is associated to K and hence to M. It cannot be
   minimal in the support of M, so it is embedded. Thus f belongs to every prime in
   the support of K, K localizes to zero, and exactness of localization makes the
   localized quotient map bijective. -/
theorem exists_maximal_nowhereDense_support_quotient
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ K : Submodule R M,
      Maximal (fun L : Submodule R M =>
        IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}) K ∧
      Module.support R (M ⧸ K) = Module.support R M ∧
      (∀ p : Ideal R, p ∈ associatedPrimes R (M ⧸ K) →
        Minimal (fun q : Ideal R => q ∈ associatedPrimes R (M ⧸ K)) p) ∧
      (∀ f : R,
        (∀ p : Ideal R, p ∈ associatedPrimes R M →
          ¬ Minimal (fun q : Ideal R => q ∈ associatedPrimes R M) p → f ∈ p) →
        Function.Bijective
          (IsLocalizedModule.map (Submonoid.powers f)
            (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
            (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ K)) K.mkQ)) := by
  classical
  let K : Submodule R M := ⨅ (p : PrimeSpectrum R)
    (_ : p.asIdeal ∈ (annihilator R M).minimalPrimes),
      LinearMap.ker (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
  have hmem (m : M) : m ∈ K ↔ ∀ p : PrimeSpectrum R,
      p.asIdeal ∈ (annihilator R M).minimalPrimes →
        ∃ s ∉ p.asIdeal, s • m = 0 := by
    simp only [K, Submodule.mem_iInf, LocalizedModule.mem_ker_mkLinearMap_iff]
    rfl
  have hvan (p : PrimeSpectrum R)
      (hp : p.asIdeal ∈ (annihilator R M).minimalPrimes) : p ∉ support R K := by
    rw [notMem_support_iff']
    intro m
    obtain ⟨s, hs, he⟩ := (hmem m.val).mp m.property p hp
    exact ⟨s, hs, Subtype.ext he⟩
  have hnd := (nowhereDense_support_iff K).mpr hvan
  have hgreat (L : Submodule R M)
      (hL : IsNowhereDense {p : support R M | p.val ∈ support R L}) : L ≤ K := by
    intro m hm
    apply (hmem m).mpr
    intro p hp
    obtain ⟨s, hs, he⟩ := (notMem_support_iff'.mp
      ((nowhereDense_support_iff L).mp hL p hp)) ⟨m, hm⟩
    exact ⟨s, hs, congrArg Subtype.val he⟩
  refine ⟨K, ⟨hnd, fun L hL _ ↦ hgreat L hL⟩, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
      (support_subset_of_surjective K.mkQ K.mkQ_surjective)
    intro p hp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
      (annihilator_le_of_mem_support hp)
    let q' : PrimeSpectrum R := ⟨q, hq.isPrime⟩
    have hqM : q' ∈ support R M := mem_support_iff_of_finite.mpr hq.le
    have hex : support R M = support R K ∪ support R (M ⧸ K) :=
      support_of_exact (LinearMap.exact_subtype_mkQ K) K.subtype_injective K.mkQ_surjective
    have hqQ : q' ∈ support R (M ⧸ K) :=
      (hex ▸ hqM).resolve_left (hvan q' hq)
    exact mem_support_mono hqp hqQ
  · intro q hq
    obtain ⟨_, x, hx⟩ := isAssociatedPrime_iff.mp hq
    obtain ⟨m, rfl⟩ := K.mkQ_surjective x
    have hm : m ∉ K := by
      intro hm
      have he : K.mkQ m = 0 := (Submodule.Quotient.mk_eq_zero K).mpr hm
      apply hq.isPrime.ne_top
      simp [hx, he]
    obtain ⟨p, hp, hmp⟩ : ∃ p : PrimeSpectrum R,
        p.asIdeal ∈ (annihilator R M).minimalPrimes ∧
          ∀ s ∉ p.asIdeal, s • m ≠ 0 := by
      rw [hmem] at hm
      push Not at hm
      exact hm
    have hqp : q ≤ p.asIdeal := by
      intro r hr
      by_contra hrp
      have hrm : r • m ∈ K := by
        apply (Submodule.Quotient.mk_eq_zero K).mp
        change K.mkQ (r • m) = 0
        simpa only [map_smul] using
          (show r • K.mkQ m = 0 from (Submodule.mem_colon_singleton.mp (hx ▸ hr)))
      obtain ⟨s, hs, he⟩ := (hmem (r • m)).mp hrm p hp
      exact hmp (s * r) (fun h ↦ (p.isPrime.mul_mem_iff_mem_or_mem.mp h).elim hs hrp)
        (by simpa only [mul_smul] using he)
    have hqann : annihilator R M ≤ q := by
      exact annihilator_le_of_mem_support
        (support_subset_of_surjective K.mkQ K.mkQ_surjective (associated_mem_support q hq))
    have hpmin : Minimal (fun r : Ideal R ↦ r.IsPrime ∧ annihilator R M ≤ r)
        p.asIdeal := hp
    have heq : q = p.asIdeal := hpmin.eq_of_le ⟨hq.isPrime, hqann⟩ hqp
    refine ⟨hq, fun r hr hrq ↦ ?_⟩
    rw [heq]
    exact hp.2 ⟨hr.isPrime, annihilator_le_of_mem_support
      (support_subset_of_surjective K.mkQ K.mkQ_surjective (associated_mem_support r hr))⟩
      (hrq.trans heq.le)
  · intro f hf
    have hzero : Subsingleton (LocalizedModule (Submonoid.powers f) K) := by
      apply LocalizedModule.subsingleton_iff_support_subset.mpr
      intro p hp
      obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
        (annihilator_le_of_mem_support hp)
      have hqK := associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R K hq
      have hqM : q ∈ associatedPrimes R M :=
        _root_.associatedPrimes.subset_of_injective K.subtype_injective hqK
      have hqnot : ¬ Minimal (fun r : Ideal R ↦ r ∈ associatedPrimes R M) q := by
        intro hmin
        exact hvan ⟨q, hq.isPrime⟩ ((minimal_associated_iff q hqM).mp hmin)
          (associated_mem_support q hqK)
      simpa only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
        using hqp (hf q hqM hqnot)
    refine ⟨?_, IsLocalizedModule.map_surjective (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ K)) K.mkQ K.mkQ_surjective⟩
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_localizedMap_eq_localized₀_ker, Submodule.ker_mkQ]
    apply le_antisymm _ bot_le
    rintro x ⟨m, hm, s, rfl⟩
    have he : ∃ r ∈ Submonoid.powers f, r • (⟨m, hm⟩ : K) = 0 :=
      LocalizedModule.subsingleton_iff.mp hzero ⟨m, hm⟩
    obtain ⟨r, hr, he⟩ := he
    have hmzero : LocalizedModule.mkLinearMap (Submonoid.powers f) M m = 0 :=
      (LocalizedModule.mem_ker_mkLinearMap_iff).mpr ⟨r, hr, congrArg Subtype.val he⟩
    change IsLocalizedModule.mk' _ m s = 0
    rw [IsLocalizedModule.mk'_eq_zero]
    exact hmzero

end Module
