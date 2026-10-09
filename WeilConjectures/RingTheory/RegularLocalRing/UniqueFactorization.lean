/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import WeilConjectures.Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import WeilConjectures.Mathlib.RingTheory.PicardGroup
public import WeilConjectures.Mathlib.RingTheory.Regular.ProjectiveDimension
public import WeilConjectures.Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# Regular local rings are UFDs

We prove the Auslander–Buchsbaum theorem (Stacks Project Tag 0AG0): a regular local ring is a
unique factorization domain. Since the localization of a regular local ring at a prime is not yet
known to be regular, we assume in addition that `R` is a regular ring (`IsRegularRing R`).

The proof (Matsumura, Theorem 20.3) is by induction on `d = dim R`. If `d = 0`, then `R` is a field.
Otherwise pick `x ∈ 𝔪 \ 𝔪²`; then `R ⧸ (x)` is regular, so `x` is a prime element, and by Nagata's
criterion it suffices to show that `A = R[1/x]` is a UFD. For this, it suffices that every prime
`P` of `A` minimal over a nonzero principal ideal is principal. The localizations of `A` at primes
are localizations of `R` at primes `𝔮 ≠ 𝔪`, which are UFDs by induction, so `P` is locally
principal, hence an invertible `A`-module. On the other hand `P` is the localization of the ideal
`P ∩ R`, which has finite projective dimension over `R`; hence `P` is stably free. An invertible
stably free module is free, so `P` is principal.

## Main results

- `IsRegularLocalRing.uniqueFactorizationMonoid`: a regular local ring which is a regular ring is a
  UFD.
-/

@[expose] public section

universe u

open IsLocalRing

/-- Let `P` be a prime ideal of a domain `A`, minimal over a nonzero principal ideal `(f)`, and `𝔮`
a prime ideal such that `A_𝔮` is a UFD. Then `P` is principal near `𝔮`: there is `0 ≠ a ∈ P` such
that every `b ∈ P` satisfies `a ∣ s * b` for some `s ∉ 𝔮`. -/
theorem Ideal.exists_forall_dvd_mul_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsDomain A]
    {f : A} (hf : f ≠ 0) {P : Ideal A} (hP : P ∈ (Ideal.span {f}).minimalPrimes) (𝔮 : Ideal A)
    [𝔮.IsPrime] [UniqueFactorizationMonoid (Localization.AtPrime 𝔮)] :
    ∃ a ∈ P, a ≠ 0 ∧ ∀ b ∈ P, ∃ s ∉ 𝔮, a ∣ s * b := by
  classical
  by_cases hP𝔮 : P ≤ 𝔮
  swap
  · obtain ⟨a, haP, ha𝔮⟩ := SetLike.not_le_iff_exists.1 hP𝔮
    exact ⟨a, haP, fun h ↦ ha𝔮 (h ▸ zero_mem _), fun b _ ↦ ⟨a, ha𝔮, dvd_mul_right a b⟩⟩
  let L := Localization.AtPrime 𝔮
  have hPprime : P.IsPrime := hP.1.1
  have hdisj : Disjoint (𝔮.primeCompl : Set A) P :=
    Set.disjoint_left.2 fun _ hx hxP ↦ hx (hP𝔮 hxP)
  have hPL := IsLocalization.isPrime_of_isPrime_disjoint 𝔮.primeCompl L P hPprime hdisj
  have hcomap := IsLocalization.under_map_of_isPrime_disjoint 𝔮.primeCompl L hPprime hdisj
  have inj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L 𝔮.primeCompl_le_nonZeroDivisors
  have hf0 : algebraMap A L f ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A L)]
    exact inj.ne hf
  obtain ⟨p, hpf, hp, hpP⟩ : ∃ p, p ∣ algebraMap A L f ∧ Prime p ∧
      p ∈ P.map (algebraMap A L) := by
    have hmem : (UniqueFactorizationMonoid.factors (algebraMap A L f)).prod ∈
        P.map (algebraMap A L) :=
      Ideal.mem_of_dvd _ (UniqueFactorizationMonoid.factors_prod hf0).symm.dvd
        (Ideal.mem_map_of_mem _ (hP.1.2 (Ideal.mem_span_singleton_self f)))
    obtain ⟨p, hp, hpP⟩ := (hPL.multiset_prod_mem_iff_exists_mem _).1 hmem
    exact ⟨p, UniqueFactorizationMonoid.dvd_of_mem_factors hp,
      UniqueFactorizationMonoid.prime_of_factor p hp, hpP⟩
  let Q := (Ideal.span {p}).comap (algebraMap A L)
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  have hQP : Q ≤ P := by
    rw [← hcomap]
    exact Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).2 hpP)
  have hfQ : Ideal.span {f} ≤ Q :=
    (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 hpf))
  have hPQ : P = Q := le_antisymm (hP.2 ⟨Ideal.comap_isPrime _ _, hfQ⟩ hQP) hQP
  have hmap : P.map (algebraMap A L) = Ideal.span {p} := by
    rw [hPQ]
    exact IsLocalization.map_under 𝔮.primeCompl L _
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj 𝔮.primeCompl p
  have haP : a ∈ P := by
    rw [hPQ, Ideal.mem_comap, ← hat]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self p)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, (IsLocalization.map_units L t).mul_left_eq_zero] at hat
    exact hp.ne_zero hat
  refine ⟨a, haP, ha0, fun b hb ↦ ?_⟩
  have hbL : algebraMap A L b ∈ Ideal.span {p} := hmap ▸ Ideal.mem_map_of_mem _ hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hbL
  obtain ⟨⟨d, u⟩, hdu⟩ := IsLocalization.surj 𝔮.primeCompl c
  refine ⟨t * u, (𝔮.primeCompl.mul_mem t.2 u.2 :), d, inj ?_⟩
  simp only at hat hdu
  rw [map_mul, map_mul, map_mul, ← hc, ← hat, ← hdu]
  ring

/-- Let `I` be a finitely generated ideal, `𝔮` a prime ideal and `a` an element such that every
`b ∈ I` satisfies `a ∣ s * b` for some `s ∉ 𝔮`. Then a single `s ∉ 𝔮` works for all `b ∈ I`. -/
theorem Ideal.exists_notMem_forall_dvd_mul {A : Type*} [CommRing A] {I 𝔮 : Ideal A} [𝔮.IsPrime]
    (hI : I.FG) {a : A} (h : ∀ b ∈ I, ∃ s ∉ 𝔮, a ∣ s * b) : ∃ s ∉ 𝔮, ∀ b ∈ I, a ∣ s * b := by
  suffices ∀ J : Ideal A, J.FG → J ≤ I → ∃ s ∉ 𝔮, ∀ b ∈ J, a ∣ s * b from this I hI le_rfl
  intro J hJ
  induction J, hJ using Submodule.fg_induction with
  | singleton y =>
    intro hyI
    obtain ⟨s, hs, hsy⟩ := h y (hyI (Submodule.mem_span_singleton_self y))
    refine ⟨s, hs, fun b hb ↦ ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    rw [mul_left_comm]
    exact hsy.mul_left r
  | sup J₁ J₂ _ _ ih₁ ih₂ =>
    intro hJI
    obtain ⟨s₁, hs₁, h₁⟩ := ih₁ (le_sup_left.trans hJI)
    obtain ⟨s₂, hs₂, h₂⟩ := ih₂ (le_sup_right.trans hJI)
    refine ⟨s₁ * s₂, fun hs ↦ (Ideal.IsPrime.mem_or_mem ‹_› hs).elim hs₁ hs₂, fun b hb ↦ ?_⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hb
    have e : s₁ * s₂ * (y + z) = s₂ * (s₁ * y) + s₁ * (s₂ * z) := by ring
    rw [e]
    exact dvd_add ((h₁ y hy).mul_left _) ((h₂ z hz).mul_left _)

namespace IsRegularLocalRing

/-- A local ring which is a regular ring and whose maximal ideal is generated by `n` elements is
a UFD. This is proved by strong induction on `n`, see the module docstring. -/
theorem uniqueFactorizationMonoid_of_spanFinrank_eq (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsRegularRing R],
      (maximalIdeal R).spanFinrank = n → UniqueFactorizationMonoid R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R _ _ _ hn
  have := IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
  -- the localizations of `R` at primes `q ≠ 𝔪` are UFDs by induction
  have hloc (q : Ideal R) [q.IsPrime] (hq : q ≠ maximalIdeal R) :
      UniqueFactorizationMonoid (Localization.AtPrime q) := by
    refine ih (maximalIdeal (Localization.AtPrime q)).spanFinrank ?_ (Localization.AtPrime q) rfl
    have h1 : ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime q) :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q] at h1
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
      (lt_of_le_of_ne (le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) hq)
    have h3 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, hn] at h3
    have h1' : ((maximalIdeal (Localization.AtPrime q)).spanFinrank : ℕ∞) = q.height := by
      exact_mod_cast h1
    have h3' : (maximalIdeal R).height = n := by exact_mod_cast h3
    rw [← h1', h3'] at h2
    exact_mod_cast (ENat.add_one_le_iff (ENat.natCast_ne_top _)).1 h2
  by_cases hfield : IsField R
  · let := hfield.toField
    infer_instance
  have hm : maximalIdeal R ≠ ⊥ := fun h ↦ hfield (isField_iff_maximalIdeal_eq.2 h)
  obtain ⟨x, hxm, hx2⟩ : ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 := by
    by_contra! h
    exact hm (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      (maximalIdeal R).fg_of_isNoetherianRing (by rw [smul_eq_mul, ← pow_two]; exact h)
      (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]))
  have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
  obtain ⟨_, _, -⟩ := IsRegularLocalRing.quotient_span_singleton hxm hx2
  have hx : Prime x := (Ideal.span_singleton_prime hx0).1
    ((Ideal.Quotient.isDomain_iff_prime _).1 inferInstance)
  let A := Localization.Away x
  have : IsDomain A :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  suffices UniqueFactorizationMonoid A from
    UniqueFactorizationMonoid.of_isLocalization_away hx A
  refine UniqueFactorizationMonoid.of_forall_isPrincipal_of_mem_minimalPrimes fun f hf P hP ↦ ?_
  -- `P` is locally principal, hence invertible
  have hinv : Module.Invertible A P := by
    refine Ideal.invertible_of_forall_isMaximal P fun 𝔮 h𝔮 ↦ ?_
    have : UniqueFactorizationMonoid (Localization.AtPrime 𝔮) := by
      have hq : 𝔮.comap (algebraMap R A) ≠ maximalIdeal R := fun h ↦ by
        have : algebraMap R A x ∈ 𝔮 := by
          rw [← Ideal.mem_comap, h]
          exact hxm
        exact h𝔮.ne_top (Ideal.eq_top_of_isUnit_mem _ this
          (IsLocalization.Away.algebraMap_isUnit x))
      have := hloc _ hq
      exact MulEquiv.uniqueFactorizationMonoid
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization _ 𝔮).toMulEquiv this
    obtain ⟨a, haP, ha0, h'⟩ := Ideal.exists_forall_dvd_mul_of_mem_minimalPrimes hf hP 𝔮
    obtain ⟨s, hs, hs'⟩ := Ideal.exists_notMem_forall_dvd_mul (IsNoetherian.noetherian P) h'
    exact ⟨a, haP, ha0, s, hs, hs'⟩
  -- `P` is the localization of `P ∩ R`, which has finite projective dimension, so `P` is
  -- stably free
  let p := P.comap (algebraMap R A)
  have hP' : Submodule.localized' A (Submonoid.powers x) (Algebra.linearMap R A) p = P := by
    rw [Ideal.localized'_eq_map]
    exact IsLocalization.map_under (Submonoid.powers x) A P
  have : Module.Invertible A
      (Submodule.localized' A (Submonoid.powers x) (Algebra.linearMap R A) p) :=
    .congr (LinearEquiv.ofEq _ _ hP'.symm)
  obtain ⟨d, hd⟩ := IsRegularLocalRing.exists_hasProjectiveDimensionLE (ModuleCat.of R p)
  have : Module.IsStablyFree A
      (Submodule.localized' A (Submonoid.powers x) (Algebra.linearMap R A) p) :=
    Module.isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE (Submonoid.powers x) d p
      hd _ (p.toLocalized' A (Submonoid.powers x) (Algebra.linearMap R A))
  have := Module.free_of_isStablyFree_of_invertible A
    (Submodule.localized' A (Submonoid.powers x) (Algebra.linearMap R A) p)
  obtain ⟨e⟩ := Module.Invertible.free_iff_linearEquiv.1 this
  rw [← hP']
  exact ⟨_, Submodule.eq_span_singleton_of_surjective e.symm.surjective⟩

/-- **Auslander–Buchsbaum theorem**: a regular local ring is a UFD. Since localizations of regular
local rings are not yet known to be regular, we assume that `R` is also a regular ring. -/
@[stacks 0AG0]
theorem uniqueFactorizationMonoid (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsRegularRing R] : UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_spanFinrank_eq _ R rfl

end IsRegularLocalRing
