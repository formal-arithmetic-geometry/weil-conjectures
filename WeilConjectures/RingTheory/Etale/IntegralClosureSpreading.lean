/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Spreading out the integral closure in a finite étale algebra over the generic fibre

Let `R` be an integrally closed domain with fraction field `K`, let `B` be a smooth Noetherian
`R`-algebra and let `L` be a finite étale algebra over `B_K = K ⊗_R B`. Then there is a nonzero
`a ∈ R` such that the integral closure of `B_a` in `L` is étale over `B_a`
(`Algebra.exists_etale_integralClosure_of_isLocalization`).

This is the commutative algebra behind the generic step of the proof of the spreading theorem
(blueprint `sbc-thm-spreading-finite-etale-galois`, [Stacks 0EYJ]).

## Main results

- `integralClosure_eq_bot_of_smooth_of_isLocalization`: a smooth algebra `E` over an integrally
  closed domain `R` is integrally closed in its localization at the nonzero elements of `R`.
- `Algebra.exists_etale_integralClosure_of_isLocalization`: the spreading statement above.
-/

@[expose] public section

open TensorProduct

/-- Criterion for `L` to be the localization of `T` at a submonoid `N`, when `T → L` is
injective. -/
lemma IsLocalization.of_injective {T L : Type*} [CommRing T] [CommRing L] [Algebra T L]
    (N : Submonoid T) (hunit : ∀ n ∈ N, IsUnit (algebraMap T L n))
    (hinj : Function.Injective (algebraMap T L))
    (hsurj : ∀ l : L, ∃ n ∈ N, ∃ t : T, algebraMap T L t = algebraMap T L n * l) :
    IsLocalization N L where
  map_units n := hunit n.1 n.2
  surj l := by
    obtain ⟨n, hn, t, ht⟩ := hsurj l
    exact ⟨⟨t, ⟨n, hn⟩⟩, by rw [ht, mul_comm]⟩
  exists_of_eq {x y} h := ⟨1, by rw [hinj h]⟩

section IntegralClosure

variable {R E L : Type*} [CommRing R] [CommRing E] [CommRing L] [Algebra R E] [Algebra E L]

/-- A smooth algebra `E` over an integrally closed domain `R` is integrally closed in its
localization `L` at the nonzero elements of `R`: smooth base change preserves integral closure
(`TensorProduct.toIntegralClosure_bijective_of_smooth`) and `R` is integrally closed in its
fraction field. -/
theorem integralClosure_eq_bot_of_smooth_of_isLocalization [IsDomain R] [IsIntegrallyClosed R]
    [Algebra.Smooth R E] [IsLocalization (Algebra.algebraMapSubmonoid E (nonZeroDivisors R)) L] :
    integralClosure E L = ⊥ := by
  let K := FractionRing R
  let : Algebra R L := ((algebraMap E L).comp (algebraMap R E)).toAlgebra
  have : IsScalarTower R E L := .of_algebraMap_eq' rfl
  have hunit : ∀ y : nonZeroDivisors R, IsUnit (algebraMap R L y) := fun y ↦ by
    rw [IsScalarTower.algebraMap_apply R E L]
    exact IsLocalization.map_units L
      (⟨algebraMap R E y, Algebra.mem_algebraMapSubmonoid_of_mem y⟩ :
        Algebra.algebraMapSubmonoid E (nonZeroDivisors R))
  let : Algebra K L := (IsLocalization.lift (M := nonZeroDivisors R) (S := K) hunit).toAlgebra
  have : IsScalarTower R K L := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq]
  have : Algebra.IsPushout R E K L :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors R) K).mp inferInstance
  let e : E ⊗[R] K ≃ₐ[E] L := Algebra.IsPushout.equiv R E K L
  have hbij := TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := E) (B := K)
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  have hx' : IsIntegral E (e.symm x) := hx.map e.symm
  obtain ⟨t, ht⟩ := hbij.2 ⟨e.symm x, hx'⟩
  have key : ∀ t : E ⊗[R] integralClosure R K,
      ((TensorProduct.toIntegralClosure R E K t : E ⊗[R] K)) ∈
        (⊥ : Subalgebra E (E ⊗[R] K)) := by
    intro t
    induction t with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul a k =>
      obtain ⟨r, hr⟩ : (k : K) ∈ (⊥ : Subalgebra R K) := by
        rw [← IsIntegrallyClosed.integralClosure_eq_bot R K]; exact k.2
      have hr' : algebraMap R K r = k := hr
      refine ⟨a * algebraMap R E r, ?_⟩
      change (a * algebraMap R E r) ⊗ₜ[R] (1 : K) = a ⊗ₜ[R] (k : K)
      rw [← hr', mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
        Algebra.algebraMap_eq_smul_one]
  have := key t
  rw [ht] at this
  obtain ⟨y, hy⟩ := this
  refine ⟨y, ?_⟩
  have := congr(e $hy)
  simpa using this

end IntegralClosure

namespace Algebra

/-- If a formally étale `B`-algebra `L` is the localization of a finitely presented `B`-algebra
`T` at a submonoid `N`, then `T` becomes étale over `B` after inverting a single element of `N`:
the étale locus of `T` is open and contains every prime disjoint from `N`. -/
theorem exists_etale_localizationAway_of_isLocalization {B T L : Type*} [CommRing B]
    [CommRing T] [CommRing L] [Algebra B T] [Algebra T L] [Algebra B L] [IsScalarTower B T L]
    [Algebra.FinitePresentation B T] [Algebra.FormallyEtale B L] (N : Submonoid T)
    [IsLocalization N L] : ∃ m ∈ N, Algebra.Etale B (Localization.Away m) := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp
    (Algebra.isOpen_etaleLocus (R := B) (A := T)).isClosed_compl
  have hmem : ∃ m ∈ N, m ∈ I := by
    by_contra! H
    obtain ⟨P, hP, hIP, hdisj⟩ := Ideal.exists_le_prime_disjoint I N (by
      rw [Set.disjoint_left]
      exact fun x hx hxN ↦ H x hxN hx)
    have hPmem : (⟨P, hP⟩ : PrimeSpectrum T) ∈ (Algebra.etaleLocus B T)ᶜ := by
      rw [hI]; exact hIP
    apply hPmem
    let p' := P.map (algebraMap T L)
    have hp' : p'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint N L P hP hdisj.symm
    have hcomap : p'.comap (algebraMap T L) = P :=
      IsLocalization.under_map_of_isPrime_disjoint N L hP hdisj.symm
    have : IsLocalization.AtPrime (Localization.AtPrime p') P := by
      have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization N
        (Localization.AtPrime p') p'
      convert this using 2
      exact hcomap.symm
    let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
      (Localization.AtPrime p')
    change Algebra.FormallyEtale B (Localization.AtPrime P)
    exact .of_equiv (e.symm.restrictScalars B)
  obtain ⟨m, hm, hmI⟩ := hmem
  refine ⟨m, hm, ?_⟩
  rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
  intro Q hQ
  by_contra hQ'
  have : Q ∈ (Algebra.etaleLocus B T)ᶜ := hQ'
  rw [hI] at this
  exact hQ (this hmI)


variable {R B Bk L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing B] [Algebra R B] [Algebra.Smooth R B] [IsNoetherianRing B]
  [CommRing Bk] [Algebra B Bk]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) Bk]
  [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]
  [Module.Finite Bk L] [Algebra.Etale Bk L]
omit [IsDomain R] [IsIntegrallyClosed R] [Algebra.Smooth R B] [IsNoetherianRing B]
  [Algebra.Etale Bk L] in
include Bk in
/-- Every element of `L` becomes, after multiplication by a nonzero element of `R`, an element of
some finite `B`-subalgebra `L₀` of `L`. -/
private lemma exists_subalgebra_finite :
    ∃ L₀ : Subalgebra B L, Module.Finite B L₀ ∧
      ∀ l : L, ∃ a ∈ nonZeroDivisors R, algebraMap B L (algebraMap R B a) * l ∈ L₀ := by
  set M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Bk) (M := L)
  have hint (x : L) : ∃ m : M, IsIntegral B (m • x) :=
    IsIntegral.exists_multiple_integral_of_isLocalization M x
      (Algebra.IsIntegral.isIntegral (R := Bk) x)
  choose m hm using hint
  let t : Set L := (fun x ↦ m x • x) '' (s : Set L)
  have ht : t.Finite := s.finite_toSet.image _
  have htint : ∀ y ∈ t, IsIntegral B y := by
    rintro _ ⟨x, -, rfl⟩; exact hm x
  refine ⟨Algebra.adjoin B t, Algebra.finite_adjoin_of_finite_of_isIntegral ht htint, fun l ↦ ?_⟩
  have hl : l ∈ Submodule.span Bk (s : Set L) := hs ▸ Submodule.mem_top
  induction hl using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, hax⟩ := (m x).2
    refine ⟨a, ha, ?_⟩
    rw [hax, ← Algebra.smul_def]
    exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, ?_⟩
    have : algebraMap B L (algebraMap R B (a * b)) * (x + y) =
        algebraMap B L (algebraMap R B b) * (algebraMap B L (algebraMap R B a) * x) +
        algebraMap B L (algebraMap R B a) * (algebraMap B L (algebraMap R B b) * y) := by
      simp only [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hax)
      (mul_mem (Subalgebra.algebraMap_mem _ _) hby)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨b, ⟨_, ⟨a', ha', rfl⟩⟩⟩, hc⟩ := IsLocalization.surj M c
    refine ⟨a' * a, mul_mem ha' ha, ?_⟩
    have : algebraMap B L (algebraMap R B (a' * a)) * (c • x) =
        algebraMap B L b * (algebraMap B L (algebraMap R B a) * x) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply B Bk L b, ← hc]
      simp only [map_mul, ← IsScalarTower.algebraMap_apply]; ring
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) hax

omit [IsNoetherianRing B] [Module.Finite Bk L] [Algebra.Etale Bk L] in
include Bk in
/-- The last step of `Algebra.exists_etale_integralClosure_of_isLocalization`: if `L₀ ⊆ L` is a
finite `B`-subalgebra with `L = L₀[1/R⁰]` and `L₀[1/a]` étale over `B`, then the integral closure
of `B' = B[1/a]` in `L` is `L₀[1/a]`, which is étale over `B'`. -/
private lemma etale_integralClosure_of_subalgebra (L₀ : Subalgebra B L) [Module.Finite B L₀]
    (hL₀ : ∀ l : L, ∃ a ∈ nonZeroDivisors R, algebraMap B L (algebraMap R B a) * l ∈ L₀)
    (a : R) (B' : Type*) [CommRing B'] [Algebra B B'] [IsLocalization.Away (algebraMap R B a) B']
    [Algebra B' L] [IsScalarTower B B' L]
    [Algebra.Etale B (Localization.Away (algebraMap B L₀ (algebraMap R B a)))] :
    Algebra.Etale B' (integralClosure B' L) := by
  set M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  have hunitL (a : R) (ha : a ∈ nonZeroDivisors R) :
      IsUnit (algebraMap B L (algebraMap R B a)) := by
    rw [IsScalarTower.algebraMap_apply B Bk L]
    exact (IsLocalization.map_units Bk
      (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, ha⟩ : nonZeroDivisors R)⟩ : M)).map _
  set r : L := algebraMap B L (algebraMap R B a)
  set m : L₀ := algebraMap B L₀ (algebraMap R B a)
  have hb : IsUnit (algebraMap B B' (algebraMap R B a)) :=
    IsLocalization.Away.algebraMap_isUnit _
  let E := Algebra.adjoin B' (L₀ : Set L)
  have hL0E : L₀ ≤ E.restrictScalars B := fun x hx ↦ Algebra.subset_adjoin hx
  have hEint : E ≤ integralClosure B' L := by
    refine Algebra.adjoin_le fun x hx ↦ ?_
    have : IsIntegral B (⟨x, hx⟩ : L₀) := Algebra.IsIntegral.isIntegral _
    exact (this.map L₀.val).tower_top
  let ι : L₀ →ₐ[B] E := Subalgebra.inclusion hL0E
  let : Algebra L₀ E := ι.toRingHom.toAlgebra
  have : IsScalarTower B L₀ E := .of_algebraMap_eq fun b ↦ (ι.commutes b).symm
  have hrE : IsUnit (algebraMap L₀ E m) := by
    have : algebraMap L₀ E m = algebraMap B' E (algebraMap B B' (algebraMap R B a)) := by
      apply Subtype.ext
      change r = _
      simp [r, ← IsScalarTower.algebraMap_apply]
    rw [this]; exact hb.map _
  have hEloc : IsLocalization.Away m E := by
    refine IsLocalization.of_injective _ ?_ (Subalgebra.inclusion_injective hL0E) fun y ↦ ?_
    · rintro _ ⟨n, rfl⟩
      rw [map_pow]; exact hrE.pow n
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, r ^ k * y.1 ∈ L₀ := by
        induction y.2 using Algebra.adjoin_induction with
        | mem x hx => exact ⟨0, by simpa using hx⟩
        | algebraMap x =>
          obtain ⟨n, b, hnb⟩ := IsLocalization.Away.surj (algebraMap R B a) x
          refine ⟨n, ?_⟩
          have : r ^ n * algebraMap B' L x = algebraMap B L b := by
            rw [IsScalarTower.algebraMap_apply B B' L b, ← hnb]
            simp [r, mul_comm, ← IsScalarTower.algebraMap_apply]
          rw [this]; exact Subalgebra.algebraMap_mem _ _
        | add x y _ _ hx hy =>
          obtain ⟨k, hk⟩ := hx
          obtain ⟨l, hl⟩ := hy
          refine ⟨k + l, ?_⟩
          rw [pow_add, mul_add]
          convert add_mem (mul_mem (pow_mem (L₀.algebraMap_mem (algebraMap R B a)) l) hk)
            (mul_mem (pow_mem (L₀.algebraMap_mem (algebraMap R B a)) k) hl) using 1
          ring
        | mul x y _ _ hx hy =>
          obtain ⟨k, hk⟩ := hx
          obtain ⟨l, hl⟩ := hy
          refine ⟨k + l, ?_⟩
          rw [pow_add]
          convert mul_mem hk hl using 1
          ring
      refine ⟨m ^ k, ⟨k, rfl⟩, ⟨_, hk⟩, ?_⟩
      apply Subtype.ext
      simp [ι, m, r]
      rfl
  have : Algebra.Etale B E :=
    .of_equiv ((IsLocalization.algEquiv (Submonoid.powers m) (Localization.Away m) E).restrictScalars
      B)
  have : Algebra.Etale B B' := .of_isLocalizationAway (algebraMap R B a)
  have : Algebra.Etale B' E := .of_restrictScalars B B' E
  let : Algebra R E := ((algebraMap B E).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B E := .of_algebraMap_eq' rfl
  have : Algebra.Smooth R E := .comp R B E
  have : IsLocalization (Algebra.algebraMapSubmonoid E (nonZeroDivisors R)) L := by
    refine IsLocalization.of_injective _ ?_ Subtype.val_injective fun l ↦ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hunitL a ha
    · obtain ⟨a, ha, hal⟩ := hL₀ l
      exact ⟨_, ⟨a, ha, rfl⟩, ⟨_, hL0E hal⟩, rfl⟩
  have hbot := integralClosure_eq_bot_of_smooth_of_isLocalization (R := R) (E := E) (L := L)
  have hEq : integralClosure B' L = E := by
    refine le_antisymm (fun x hx ↦ ?_) hEint
    have hx' : IsIntegral E x := IsIntegral.tower_top hx
    have : x ∈ integralClosure E L := hx'
    rw [hbot] at this
    obtain ⟨y, rfl⟩ := this
    exact y.2
  exact .of_equiv (Subalgebra.equivOfEq _ _ hEq.symm)


include Bk in
/-- The generic step of the proof of [Stacks 0EYJ] (blueprint
`sbc-thm-spreading-finite-etale-galois`), in commutative algebra: let `R` be an integrally
closed domain, `B` a smooth Noetherian `R`-algebra, `B_K` its localization at the nonzero elements
of `R` and `L` a finite étale `B_K`-algebra. Then there is a nonzero `a ∈ R` such that for every
localization `B'` of `B` away from `a` and every copy `L'` of `L` (as a `B`-algebra) which is a
`B'`-algebra, the integral closure of `B'` in `L'` is étale over `B'`. -/
theorem exists_etale_integralClosure_of_isLocalization :
    ∃ a ∈ nonZeroDivisors R, ∀ (B' L' : Type*) [CommRing B'] [CommRing L'] [Algebra B B']
      [IsLocalization.Away (algebraMap R B a) B'] [Algebra B' L'] [Algebra B L']
      [IsScalarTower B B' L'] (_ : L ≃ₐ[B] L'), Algebra.Etale B' (integralClosure B' L') := by
  obtain ⟨L₀, hfin, hL₀⟩ := exists_subalgebra_finite (R := R) (B := B) (Bk := Bk) (L := L)
  have : FinitePresentation B L₀ := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  set M := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  have hunitL (a : R) (ha : a ∈ nonZeroDivisors R) :
      IsUnit (algebraMap B L (algebraMap R B a)) := by
    rw [IsScalarTower.algebraMap_apply B Bk L]
    exact (IsLocalization.map_units Bk
      (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, ha⟩ : nonZeroDivisors R)⟩ : M)).map _
  have : IsLocalization (Algebra.algebraMapSubmonoid L₀ M) L := by
    refine IsLocalization.of_injective _ ?_ Subtype.val_injective fun l ↦ ?_
    · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact hunitL a ha
    · obtain ⟨a, ha, hal⟩ := hL₀ l
      exact ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, ⟨_, hal⟩, rfl⟩
  have : FormallyEtale B L := by
    have : FormallyEtale B Bk := .of_isLocalization M
    exact .comp B Bk L
  obtain ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, hEtm⟩ :=
    Algebra.exists_etale_localizationAway_of_isLocalization (B := B) (L := L)
      (Algebra.algebraMapSubmonoid L₀ M)
  refine ⟨a, ha, fun B' L' _ _ _ _ _ _ _ e ↦ ?_⟩
  let : Algebra B' L := (e.symm.toRingHom.comp (algebraMap B' L')).toAlgebra
  have : IsScalarTower B B' L := .of_algebraMap_eq fun b ↦ by
    simp [RingHom.algebraMap_toAlgebra, ← IsScalarTower.algebraMap_apply]
  let e' : L ≃ₐ[B'] L' :=
    { e with commutes' := fun b ↦ by simp [RingHom.algebraMap_toAlgebra] }
  have := etale_integralClosure_of_subalgebra (Bk := Bk) L₀ hL₀ a B'
  exact .of_equiv e'.mapIntegralClosure

end Algebra
