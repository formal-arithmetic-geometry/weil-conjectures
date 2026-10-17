/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurityStep
public import WeilConjectures.RingTheory.Etale.IntegralClosureSpreading

/-!
# Spreading out finite étaleness of a normal cover of a smooth algebra

Let `R₀` be a Noetherian integrally closed domain, `B` a smooth `R₀`-algebra, `M` a `B`-algebra in
which the nonzero elements of `R₀` are invertible and `T` the integral closure of `B` in `M`. Let
`P` be a prime of `B` not over `0`, such that `T` is finite étale over a neighbourhood of every
prime `Q ⊊ P`. If `B_P ⊗_B T` is finite étale over `B_P`, then `T` is finite étale over a
neighbourhood `D(h)` of `P` (`RingTheory.DepthTwo.exists_etale_finite_away_of_localization`).

Proof. Shrinking, `B_h` is a normal domain, and every prime of `D(h)` over `0 ⊆ R₀` has a
neighbourhood over which `T` is finite étale (the locus where `T` is finite étale is open and
contains all strict generizations of `P`). Then `B_h ⊗ T` is torsion free, so it embeds into
`K ⊗ T` (`K = Frac B`), an étale `K`-algebra, and `B_h ⊗ T` is finite as it lies in the integral
closure of `B_h` (`RingTheory.DepthTwo.finite_integralClosure_of_etale`). Finally étaleness
spreads out from `B_P` (`Algebra.exists_etale_away_tensor_of_isLocalization`).

This is a step of the proof of purity for normal covers of a smooth algebra over a normal base
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open TensorProduct

namespace Algebra

/-- **Spreading out étaleness from a localization of the base.** If `X` is a finitely presented
`A`-algebra and `S⁻¹A ⊗_A X` is étale over `S⁻¹A`, then `A_s ⊗_A X` is étale over `A_s` for some
`s ∈ S`. -/
theorem exists_etale_away_tensor_of_isLocalization {A A' X : Type u} [CommRing A] [CommRing A']
    [CommRing X] [Algebra A A'] [Algebra A X] [Algebra.FinitePresentation A X]
    (S : Submonoid A) [IsLocalization S A'] [Algebra.Etale A' (A' ⊗[A] X)] :
    ∃ s ∈ S, Algebra.Etale (Localization.Away s) (Localization.Away s ⊗[A] X) := by
  let : Algebra X (A' ⊗[A] X) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid X S) (A' ⊗[A] X) :=
    IsLocalization.tensorRight _ _
  have : IsScalarTower A X (A' ⊗[A] X) := .of_algebraMap_eq fun b ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  have : Algebra.FormallyEtale A A' := .of_isLocalization S
  have : Algebra.FormallyEtale A (A' ⊗[A] X) := .comp A A' _
  obtain ⟨_, ⟨s, hs, rfl⟩, hEt⟩ := Algebra.exists_etale_localizationAway_of_isLocalization
    (B := A) (L := A' ⊗[A] X) (Algebra.algebraMapSubmonoid X S)
  refine ⟨s, hs, ?_⟩
  let Y := Localization.Away s ⊗[A] X
  let : Algebra X Y := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization.Away (algebraMap A X s) Y :=
    IsLocalization.Away.tensorRight s (Localization.Away s)
  have : IsScalarTower A X Y := .of_algebraMap_eq fun b ↦ by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  let e : Y ≃ₐ[X] Localization.Away (algebraMap A X s) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap A X s)) Y _
  have : Algebra.Etale A Y := .of_equiv (e.symm.restrictScalars A)
  exact Algebra.Etale.of_restrictScalars A (Localization.Away s) Y

end Algebra

namespace RingTheory.DepthTwo

section Locus

variable {B : Type*} [CommRing B] [IsNoetherianRing B]

/-- **Avoiding the bad locus.** Let `good` be a property of elements of a Noetherian ring `B`,
and `P` a prime such that every prime `Q ⊊ P` avoids some `good` element. Then there is `h₀ ∉ P`
such that every prime `Q ∌ h₀` not containing `P` avoids some `good` element: the closed set of
primes containing all `good` elements meets `D(h₀)` inside `V(P)`. -/
lemma exists_forall_exists_not_mem (good : B → Prop) (P : Ideal B) [P.IsPrime]
    (H : ∀ Q : Ideal B, Q.IsPrime → Q < P → ∃ h ∉ Q, good h) :
    ∃ h₀ ∉ P, ∀ Q : Ideal B, Q.IsPrime → h₀ ∉ Q → ¬ P ≤ Q → ∃ h ∉ Q, good h := by
  classical
  let I := Ideal.span {h | good h}
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
  let s := hfin.toFinset.filter fun p ↦ ¬ p ≤ P
  have hs (p : Ideal B) (hp : p ∈ s) : ∃ x ∈ p, x ∉ P := Set.not_subset.1 (Finset.mem_filter.1 hp).2
  choose! f hf using hs
  refine ⟨∏ p ∈ s, f p, ?_, fun Q hQ hQh hPQ ↦ ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hfp⟩
    exact (hf p hp).2 hfp
  · by_contra! hall
    obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := Q)
      (Ideal.span_le.2 fun h hh ↦ by_contra fun hhQ ↦ hall h hhQ hh)
    have := hp.1.1
    by_cases hpP : p ≤ P
    · rcases lt_or_eq_of_le hpP with hlt | rfl
      · obtain ⟨h, hhp, hh⟩ := H p this hlt
        exact hhp (hp.1.2 (Ideal.subset_span hh))
      · exact hPQ hpQ
    · have hps : p ∈ s := Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 hp, hpP⟩
      exact hQh ((Ideal.IsPrime.prod_mem_iff).2 ⟨p, hps, hpQ (hf p hps).1⟩)

/-- **A domain neighbourhood.** If `B` is a reduced Noetherian ring and `B_P` is a domain, then
there is `h₁ ∉ P` such that `B_{g h₁}` is a domain for every `g ∉ P`: `h₁` lies in the minimal
primes of `B` not contained in `P`, and `B_{g h₁}` embeds into `B_P`. -/
lemma exists_isDomain_away [IsReduced B] (P : Ideal B) [P.IsPrime]
    [IsDomain (Localization.AtPrime P)] :
    ∃ h₁ ∉ P, ∀ g ∉ P, IsDomain (Localization.Away (g * h₁)) := by
  classical
  let p₀ := RingHom.ker (algebraMap B (Localization.AtPrime P))
  have hp₀ : p₀.IsPrime := RingHom.ker_isPrime _
  have hker (y : B) (hy : y ∈ p₀) : ∃ s ∉ P, s * y = 0 := by
    obtain ⟨⟨s, hs⟩, hsy⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ y).1 hy
    exact ⟨s, hs, hsy⟩
  have hmin (p : Ideal B) (hp : p ∈ minimalPrimes B) (hpP : p ≤ P) : p₀ ≤ p := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := hker y hy
    exact (hp.1.1.mem_or_mem (hsy ▸ p.zero_mem)).resolve_left fun h ↦ hs (hpP h)
  have hfin := minimalPrimes.finite_of_isNoetherianRing B
  let s := hfin.toFinset.filter fun p ↦ ¬ p ≤ P
  have hs (p : Ideal B) (hp : p ∈ s) : ∃ x ∈ p, x ∉ P := Set.not_subset.1 (Finset.mem_filter.1 hp).2
  choose! f hf using hs
  refine ⟨∏ p ∈ s, f p, ?_, fun g hg ↦ ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hfp⟩
    exact (hf p hp).2 hfp
  set x := g * ∏ p ∈ s, f p
  have hxP : x ∉ P := by
    refine fun h ↦ (Ideal.IsPrime.mem_or_mem inferInstance h).elim hg fun h' ↦ ?_
    obtain ⟨p, hp, hfp⟩ := Ideal.IsPrime.prod_mem_iff.1 h'
    exact (hf p hp).2 hfp
  -- `x y = 0` for `y ∈ p₀`
  have hxy (y : B) (hy : y ∈ p₀) : x * y = 0 := by
    have hmem : x * y ∈ sInf (minimalPrimes B) := by
      refine Submodule.mem_sInf.2 fun p hp ↦ ?_
      by_cases hpP : p ≤ P
      · exact Ideal.mul_mem_left _ _ (hmin p hp hpP hy)
      · have hps : p ∈ s := Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 hp, hpP⟩
        have := hp.1.1
        refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_)
        exact Ideal.IsPrime.prod_mem_iff.2 ⟨p, hps, (hf p hps).1⟩
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    obtain ⟨n, hn⟩ := hmem
    exact IsReduced.eq_zero _ ⟨n, (Submodule.mem_bot _).1 hn⟩
  let φ : Localization.Away x →+* Localization.AtPrime P :=
    IsLocalization.Away.lift x (IsLocalization.map_units _ (⟨x, hxP⟩ : P.primeCompl))
  have hφ : Function.Injective φ := (injective_iff_map_eq_zero φ).2 fun z hz ↦ by
    obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) z
    have h1 : φ (algebraMap B _ y) = 0 := by
      rw [← IsLocalization.mk'_spec (Localization.Away x) y t, map_mul, hz, zero_mul]
    rw [IsLocalization.Away.lift_eq] at h1
    exact (IsLocalization.mk'_eq_zero_iff _ _).2 ⟨⟨x, 1, pow_one x⟩, hxy y h1⟩
  exact hφ.isDomain φ

end Locus

section Torsion

variable {R₀ B M : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [CommRing B] [Algebra R₀ B] [Algebra.Smooth R₀ B]
  [CommRing M] [Algebra B M] [Algebra R₀ M] [IsScalarTower R₀ B M]

/-- **Torsion in the integral closure.** Suppose that every prime `Q ∌ h` of `B` over `0 ⊆ R₀`
has a neighbourhood over which the integral closure `T` of `B` in `M` is finite étale. If `s ∈ B`
is nonzero in the local rings `B_Q` for `Q ∌ h`, then every `y ∈ T` with `s y = 0` is killed by a
power of `h`. -/
lemma exists_pow_smul_eq_zero (hunit : ∀ r : R₀, r ≠ 0 → IsUnit (algebraMap R₀ M r)) (h : B)
    (hgood : ∀ Q : Ideal B, Q.IsPrime → h ∉ Q → Q.comap (algebraMap R₀ B) = ⊥ →
      ∃ h' ∉ Q, Algebra.Etale (Localization.Away h')
        (Localization.Away h' ⊗[B] integralClosure B M) ∧
        Module.Finite (Localization.Away h') (Localization.Away h' ⊗[B] integralClosure B M))
    {s : B} (hs : ∀ (Q : Ideal B) [Q.IsPrime], h ∉ Q → algebraMap B (Localization.AtPrime Q) s ≠ 0)
    {y : integralClosure B M} (hy : s • y = 0) : ∃ k : ℕ, h ^ k • y = 0 := by
  by_contra! hk
  let J : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B (integralClosure B M) y)
  let S := Submonoid.powers h ⊔ Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)
  have hdisj : Disjoint (J : Set B) S := by
    rw [Set.disjoint_left]
    intro x hxJ hxS
    obtain ⟨_, ⟨k, rfl⟩, _, ⟨r, hr, rfl⟩, rfl⟩ := Submonoid.mem_sup.1 hxS
    apply hk k
    have hxy : (h ^ k * algebraMap R₀ B r) • y = 0 := hxJ
    have h2 : algebraMap R₀ B r • (h ^ k • y) = 0 := by
      rw [smul_smul, mul_comm]
      exact hxy
    apply Subtype.ext
    have h3 := congrArg Subtype.val h2
    rw [ZeroMemClass.coe_zero, SetLike.val_smul, algebraMap_smul, Algebra.smul_def] at h3
    exact ((hunit r (nonZeroDivisors.ne_zero hr)).mul_right_eq_zero).1 h3
  obtain ⟨Q, hQ, hJQ, hQS⟩ := Ideal.exists_le_prime_disjoint J S hdisj
  have hhQ : h ∉ Q := fun hh ↦ Set.disjoint_left.1 hQS hh
    (Submonoid.mem_sup_left (Submonoid.mem_powers h))
  have hQ0 : Q.comap (algebraMap R₀ B) = ⊥ := by
    refine eq_bot_iff.2 fun r hr ↦ (Submodule.mem_bot R₀).2 ?_
    by_contra hr0
    exact Set.disjoint_left.1 hQS hr (Submonoid.mem_sup_right
      ⟨r, mem_nonZeroDivisors_of_ne_zero hr0, rfl⟩)
  obtain ⟨h', hh'Q, hE, -⟩ := hgood Q hQ hhQ hQ0
  -- `B_Q ⊗ T` is flat over `B_Q`
  let BQ := Localization.AtPrime Q
  let : Algebra (Localization.Away h') BQ :=
    (IsLocalization.Away.lift h'
      (IsLocalization.map_units BQ (⟨h', hh'Q⟩ : Q.primeCompl))).toAlgebra
  have : IsScalarTower B (Localization.Away h') BQ :=
    .of_algebraMap_eq fun b ↦ (IsLocalization.Away.lift_eq h' _ b).symm
  let e := Algebra.TensorProduct.cancelBaseChange B (Localization.Away h') BQ BQ
    (integralClosure B M)
  have : Module.Flat BQ (BQ ⊗[B] integralClosure B M) := .of_linearEquiv e.symm.toLinearEquiv
  obtain ⟨hdom, -⟩ := Algebra.Smooth.isDomain_and_isIntegrallyClosed_localization R₀ B Q
  have hreg : IsSMulRegular (BQ ⊗[B] integralClosure B M) (algebraMap B BQ s) :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero (hs Q hhQ))
  have h0 : TensorProduct.mk B BQ (integralClosure B M) 1 y = 0 := by
    apply hreg
    simp only [TensorProduct.mk_apply, smul_zero]
    rw [algebraMap_smul, ← TensorProduct.tmul_smul, hy, TensorProduct.tmul_zero]
  obtain ⟨⟨w, hw⟩, hwy⟩ := (IsLocalizedModule.eq_zero_iff Q.primeCompl
    (TensorProduct.mk B BQ (integralClosure B M) 1)).1 h0
  exact hw (hJQ hwy)

end Torsion

end RingTheory.DepthTwo
