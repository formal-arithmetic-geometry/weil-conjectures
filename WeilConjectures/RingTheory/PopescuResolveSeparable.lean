/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.MvPolynomial.Ideal
import WeilConjectures.RingTheory.PopescuDelocalizeHeightZero
import WeilConjectures.RingTheory.PopescuLiftSolution
import WeilConjectures.RingTheory.PopescuResolutionSmoothBase
import WeilConjectures.RingTheory.PopescuSeparableHeightZeroLocal
import WeilConjectures.RingTheory.PopescuSeparableParameterQuotient
import WeilConjectures.RingTheory.PopescuSeparablePreparation

/-!
# Resolving Popescu's local problem with separable residue field

A finitely presented algebra over a field admits a Popescu resolution at a prime minimal over
its extended singular ideal, provided the target is Noetherian, the local ring at that prime is
regular, and its residue field is separable over the base field.

## Implementation details

The proof follows Stacks Lemma 07FE with the following repairs:

* the exponent `n` is chosen with `q^n Λ_q ⊆ H_{A/k} Λ_q` rather than `⊆ h_A Λ_q`, since the
  map `B → Λ` needs `π_i^n ∈ H_{A/k} Λ` (Stacks also writes `H_{A/R}` for `H_{A/k}`);
* the case `d = 0` is treated separately, since Lemma 07F8 needs at least one element;
* the passage from a resolution over `R = k[x]` back to `k`, and the minimality hypothesis of
  Lemma 07FA after reducing modulo `x^e`, are checked explicitly.

## References

* [Stacks, Tag 07FE]
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem power_annihilator_eq
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (c : ℕ) (hc : 1 ≤ c)
    (h : ∀ x : M, r • x = 0 ↔ r ^ 2 • x = 0) (x : M) :
    r ^ c • x = 0 ↔ (r ^ c) ^ 2 • x = 0 := by
  have hpow (n : ℕ) : ∀ x : M, r ^ (n + 1) • x = 0 ↔ r • x = 0 := by
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ r (n + 1), mul_smul, ih (r • x)]
      simpa only [pow_two, mul_smul] using (h x).symm
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, c = n + 1 := ⟨c - 1, by omega⟩
  rw [← pow_mul]
  have he : (n + 1) * 2 = (2 * n + 1) + 1 := by omega
  rw [he]
  exact (hpow n x).trans (hpow (2 * n + 1) x).symm

private theorem polynomial_pow_mem_of_mul_mem
    {k : Type u} [CommRing k] (d c m : ℕ) (i : Fin d)
    (p : MvPolynomial (Fin d) k)
    (hp : MvPolynomial.X i ^ m * p ∈ Ideal.span
      {y : MvPolynomial (Fin d) k |
        ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8}) :
    p ∈ Ideal.span {y : MvPolynomial (Fin d) k |
      ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8} := by
  classical
  let s : Set (Fin d →₀ ℕ) := {e | ∃ j : Fin d, j.val < i.val ∧
    e = Finsupp.single j (c * 8)}
  have hset : {y : MvPolynomial (Fin d) k |
      ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8} =
      (fun e : Fin d →₀ ℕ ↦ MvPolynomial.monomial e (1 : k)) '' s := by
    ext p
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finsupp.single j (c * 8), ⟨j, hj, rfl⟩, by
        rw [← pow_mul, MvPolynomial.X_pow_eq_monomial]⟩
    · rintro ⟨e, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j, hj, by rw [← pow_mul, MvPolynomial.X_pow_eq_monomial]⟩
  rw [hset] at hp ⊢
  apply MvPolynomial.mem_ideal_span_monomial_image.mpr
  intro e he
  have hs : Finsupp.single i m + e ∈ (MvPolynomial.X i ^ m * p).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.X_pow_eq_monomial,
      MvPolynomial.coeff_monomial_mul, one_mul]
    exact MvPolynomial.mem_support_iff.mp he
  obtain ⟨f, ⟨j, hj, rfl⟩, hfe⟩ :=
    MvPolynomial.mem_ideal_span_monomial_image.mp hp _ hs
  refine ⟨Finsupp.single j (c * 8), ⟨j, hj, rfl⟩, ?_⟩
  rw [Finsupp.single_le_iff] at hfe ⊢
  have hji : i ≠ j := by intro h; subst j; omega
  simpa [Finsupp.single_apply, hji] using hfe

private theorem polynomial_annihilator_eq
    {k : Type u} [CommRing k] (d c : ℕ) (i : Fin d)
    (x : MvPolynomial (Fin d) k ⧸ Ideal.span
      {y : MvPolynomial (Fin d) k |
        ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8}) :
    (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ c • x = 0 ↔
      ((MvPolynomial.X i : MvPolynomial (Fin d) k) ^ c) ^ 2 • x = 0 := by
  let J : Ideal (MvPolynomial (Fin d) k) := Ideal.span
    {y | ∃ j : Fin d, j.val < i.val ∧ y = (MvPolynomial.X j ^ c) ^ 8}
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hzero (m : ℕ) (h : (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ m •
        Ideal.Quotient.mk J p = 0) :
      Ideal.Quotient.mk J p = 0 := by
    change Ideal.Quotient.mk J (MvPolynomial.X i ^ m * p) = 0 at h
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (polynomial_pow_mem_of_mul_mem d c m i p
      (Ideal.Quotient.eq_zero_iff_mem.mp h))
  constructor
  · intro h
    rw [hzero c h, smul_zero]
  · intro h
    rw [← pow_mul] at h
    rw [hzero (c * 2) h, smul_zero]

/-- A finitely presented algebra over a field admits a Popescu resolution at a prime
minimal over its extended singular ideal, provided the target is Noetherian, the local
ring at that prime is regular, and its residue field is separable over the base field. -/
theorem canBePopescuResolved_of_regularLocalRing_separable
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes)
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    (hsep : IsSeparableExtension k q.asIdeal.ResidueField) :
    CanBePopescuResolved α q := by
  by_cases hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = 0
  · exact canBePopescuResolved_of_local_height_zero α q hminimal
      (popescu_separable_height_zero_local α q hdim hsep) hdim
  · let d := (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank
    have hdimension : ringKrullDim (Localization.AtPrime q.asIdeal) =
        (d : WithBot ℕ∞) := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
    have hd : 1 ≤ d := by
      by_contra h
      have hz : d = 0 := by omega
      exact hdim (by simpa [hz] using hdimension)
    let I := Ideal.map α.toRingHom (singularIdeal k A)
    have hIq : I ≤ q.asIdeal := Ideal.le_radical.trans hminimal.le
    have hrad : (I.map (algebraMap Λ (Localization.AtPrime q.asIdeal))).radical =
        q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) := by
      apply IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
      change q.asIdeal ∈ I.radical.minimalPrimes at hminimal
      rwa [Ideal.radical_minimalPrimes] at hminimal
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (le_of_eq hrad.symm)
      (IsNoetherian.noetherian
        (q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))))
    have hpow : (q.asIdeal ^ (n + 1)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal)) ≤
        I.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) := by
      rw [Ideal.map_pow]
      exact (Ideal.pow_le_pow_right (by omega)).trans hn
    obtain ⟨c, φ, C, instC, algkC, algRC, towerC, fpC, β, γ,
      hc, hgen, hcomp, hideal, hπ, hΛ, hstandard⟩ :=
        exists_popescu_separable_preparation α q d (n + 1) hd (by omega)
          hdimension hIq hpow
    let : Algebra (MvPolynomial (Fin d) k) Λ := φ.toRingHom.toAlgebra
    have hquotient := exists_popescu_resolution_parameter_quotient
      d c hc φ γ q hdimension hgen hsep
    have hresolved : CanBePopescuResolved γ q :=
      canBePopescuResolved_of_quotient_eighth_powers d
        (fun i : Fin d ↦ MvPolynomial.X i ^ c) γ q hd hπ (polynomial_annihilator_eq d c)
        (fun i x ↦ power_annihilator_eq (MvPolynomial.X i) c hc (hΛ i) x)
        hstandard hquotient
    have : Smooth k (MvPolynomial (Fin d) k) := Smooth.mk
    exact canBePopescuResolved_of_smooth_base α q β γ hcomp hideal hresolved

end Algebra
