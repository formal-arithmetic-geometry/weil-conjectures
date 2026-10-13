/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Finitely presented algebras mapping to a localization

## Main statements

- `Algebra.FinitePresentation.exists_comp_eq_of_localization`: an `R`-algebra map from a finitely
  presented `R`-algebra `C` to a localization `S⁻¹P` factors through a principal localization
  `P[1/s]` with `s ∈ S` (Stacks, Tags 00CR and 00QO).
-/

@[expose] public section

namespace Localization

variable {R P : Type*} [CommSemiring R] [CommRing P] [Algebra R P]

/-- The canonical `R`-algebra map `P[1/s] → P[1/t]` when `s ∣ t`. -/
noncomputable def awayMapOfDvd {s t : P} (h : s ∣ t) : Away s →ₐ[R] Away t :=
  IsLocalization.Away.liftAlgHom s (f := IsScalarTower.toAlgHom R P (Away t))
    (isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit t))

/-- The canonical `R`-algebra map `P[1/s] → S⁻¹P` for `s ∈ S`. -/
noncomputable def awayToLocalization {S : Submonoid P} {s : P} (hs : s ∈ S) :
    Away s →ₐ[R] Localization S :=
  IsLocalization.Away.liftAlgHom s (f := IsScalarTower.toAlgHom R P (Localization S))
    (IsLocalization.map_units (Localization S) ⟨s, hs⟩)

@[simp]
theorem awayMapOfDvd_algebraMap {s t : P} (h : s ∣ t) (x : P) :
    awayMapOfDvd (R := R) h (algebraMap P _ x) = algebraMap P _ x := by
  simp [awayMapOfDvd]

@[simp]
theorem awayToLocalization_algebraMap {S : Submonoid P} {s : P} (hs : s ∈ S) (x : P) :
    awayToLocalization (R := R) hs (algebraMap P _ x) = algebraMap P _ x := by
  exact IsLocalization.Away.lift_eq s (IsLocalization.map_units (Localization S) ⟨s, hs⟩) x

theorem awayToLocalization_comp_awayMapOfDvd {S : Submonoid P} {s t : P} (hs : s ∈ S)
    (ht : t ∈ S) (h : s ∣ t) :
    (awayToLocalization (R := R) ht).comp (awayMapOfDvd h) = awayToLocalization hs :=
  IsLocalization.algHom_ext (Submonoid.powers s) (AlgHom.ext fun x ↦ by
    change awayToLocalization ht (awayMapOfDvd h (algebraMap P _ x)) =
      awayToLocalization hs (algebraMap P _ x)
    simp)

/-- Every element of `S⁻¹P` comes from `P[1/s]` for all `s ∈ S` divisible by a suitable
`t ∈ S`. -/
theorem exists_forall_dvd_mem_range_awayToLocalization {S : Submonoid P} (x : Localization S) :
    ∃ t ∈ S, ∀ s (hs : s ∈ S), t ∣ s → x ∈ Set.range (awayToLocalization (R := R) hs) := by
  obtain ⟨⟨a, t, ht⟩, rfl⟩ := IsLocalization.mk'_surjective S x
  refine ⟨t, ht, fun s hs ⟨u, hu⟩ ↦ ⟨algebraMap P _ (a * u) * IsLocalization.Away.invSelf s, ?_⟩⟩
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, awayToLocalization_algebraMap]
  have hinv : awayToLocalization (R := R) hs (IsLocalization.Away.invSelf s) *
      algebraMap P (Localization S) s = 1 := by
    rw [← awayToLocalization_algebraMap (R := R) hs, ← map_mul, mul_comm,
      IsLocalization.Away.mul_invSelf, map_one]
  have hs' : algebraMap P (Localization S) s =
      algebraMap P (Localization S) t * algebraMap P (Localization S) u := by
    rw [hu, map_mul]
  simp only [map_mul]
  linear_combination (algebraMap P (Localization S) a) * hinv - algebraMap P (Localization S) a *
    awayToLocalization (R := R) hs (IsLocalization.Away.invSelf s) * hs'

/-- An element of `P[1/s]` which vanishes in `S⁻¹P` already vanishes in `P[1/t]` for every `t`
divisible by `s` and by a suitable `u ∈ S`. -/
theorem exists_forall_dvd_awayMapOfDvd_eq_zero {S : Submonoid P} {s : P} (hs : s ∈ S)
    (z : Away s) (hz : awayToLocalization (R := R) hs z = 0) :
    ∃ u ∈ S, ∀ t (h : s ∣ t), u ∣ t → awayMapOfDvd (R := R) h z = 0 := by
  obtain ⟨⟨b, _, e, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) z
  simp only at hz ⊢
  have hspec := IsLocalization.mk'_spec (Away s) b
    ⟨s ^ e, Submonoid.pow_mem _ (Submonoid.mem_powers s) e⟩
  have hb : algebraMap P (Localization S) b = 0 := by
    have := congrArg (awayToLocalization (R := R) hs) hspec
    simpa [hz] using this.symm
  obtain ⟨⟨u, hu⟩, hub⟩ := (IsLocalization.map_eq_zero_iff S _ b).mp hb
  refine ⟨u, hu, fun t h hut ↦ ?_⟩
  have hunit : IsUnit (algebraMap P (Away t) u) :=
    isUnit_of_dvd_unit (map_dvd _ hut) (IsLocalization.Away.algebraMap_isUnit t)
  have hst : IsUnit (algebraMap P (Away t) (s ^ e)) :=
    isUnit_of_dvd_unit (map_dvd _ (pow_dvd_pow_of_dvd h e))
      (by rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit t).pow e)
  have hb' : algebraMap P (Away t) b = 0 := by
    have := congrArg (algebraMap P (Away t)) hub
    rw [map_mul, map_zero] at this
    exact (hunit.mul_right_eq_zero).mp this
  have := congrArg (awayMapOfDvd (R := R) h) hspec
  rw [map_mul, awayMapOfDvd_algebraMap, awayMapOfDvd_algebraMap, hb'] at this
  exact (hst.mul_left_eq_zero).mp this

end Localization

namespace Algebra.FinitePresentation

variable {R C P : Type*} [CommRing R] [CommRing C] [CommRing P] [Algebra R C] [Algebra R P]

open Localization in
/-- Let `C` be a finitely presented `R`-algebra, `P` an `R`-algebra and `S ⊆ P` a submonoid.
Every `R`-algebra map `g : C → S⁻¹P` factors as `C → P[1/s] → S⁻¹P` for some `s ∈ S`
(blueprint: `lem-factors-through-localization-of-smooth`). -/
theorem exists_comp_eq_of_localization [Algebra.FinitePresentation R C] (S : Submonoid P)
    (g : C →ₐ[R] Localization S) :
    ∃ s ∈ S, ∃ (f : C →ₐ[R] Localization.Away s) (k : Localization.Away s →ₐ[R] Localization S),
      k.comp f = g := by
  classical
  obtain ⟨n, π, hπ, T, hT⟩ := Algebra.FinitePresentation.out (R := R) (A := C)
  choose t ht hrange using fun i : Fin n ↦
    exists_forall_dvd_mem_range_awayToLocalization (R := R) (g (π (MvPolynomial.X i)))
  set s₁ := ∏ i, t i
  have hs₁ : s₁ ∈ S := Submonoid.prod_mem _ fun i _ ↦ ht i
  choose y hy using fun i ↦ hrange i s₁ hs₁ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  let φ : MvPolynomial (Fin n) R →ₐ[R] Away s₁ := MvPolynomial.aeval y
  have hφ : (awayToLocalization hs₁).comp φ = g.comp π :=
    MvPolynomial.algHom_ext fun i ↦ by simp [φ, hy i]
  have hker : ∀ r ∈ T, awayToLocalization hs₁ (φ r) = 0 := fun r hr ↦ by
    have hr' : π r = 0 := by
      have : r ∈ RingHom.ker π.toRingHom := hT ▸ Ideal.subset_span hr
      simpa using this
    simpa [hr'] using DFunLike.congr_fun hφ r
  choose u hu hkill using fun r : T ↦
    exists_forall_dvd_awayMapOfDvd_eq_zero (R := R) hs₁ (φ r) (hker r r.2)
  set s := s₁ * ∏ r ∈ T.attach, u r
  have hs : s ∈ S := mul_mem hs₁ (Submonoid.prod_mem _ fun r _ ↦ hu r)
  have hdvd : s₁ ∣ s := dvd_mul_right _ _
  let ψ := (awayMapOfDvd (R := R) hdvd).comp φ
  have hψ : RingHom.ker π.toRingHom ≤ RingHom.ker ψ.toRingHom := by
    rw [← hT, Ideal.span_le]
    intro r hr
    exact hkill ⟨r, hr⟩ s hdvd
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_attach _ _)) _)
  refine ⟨s, hs, π.liftOfSurjective hπ ψ hψ, awayToLocalization hs, ?_⟩
  ext c
  obtain ⟨r, rfl⟩ := hπ c
  simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.liftOfSurjective_apply, ψ]
  rw [← AlgHom.comp_apply (awayToLocalization hs), awayToLocalization_comp_awayMapOfDvd hs₁,
    ← AlgHom.comp_apply, hφ, AlgHom.comp_apply]

end Algebra.FinitePresentation
