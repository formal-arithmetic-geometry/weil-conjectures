/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Polynomial.Identities
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Henselian discrete valuation rings inside `K⟦t⟧`

Let `R` be a henselian discrete valuation ring with a uniformizer `π` and `ι : R ⟶ K⟦t⟧` a local
injection with `ι π = t`.

## Main results

- `IsDiscreteValuationRing.mem_range_of_isRoot_of_forall_exists_dvd`: a simple root `y ∈ K⟦t⟧`
  of a polynomial `f` over `R` which is a `t`-adic limit of elements of `ι(R)` lies in `ι(R)`.
  With `s` the order of `f'(y)`, an approximation `z` of `y` modulo `t^{2s+1}` satisfies
  `f(z) = f'(z)² c` with `c ∈ 𝔪`, so Newton's lemma
  (`HenselianRing.exists_isRoot_of_eval_eq_sq_mul`) gives a root `b` of `f` with
  `ι b ≡ y (mod t^{s+1})`, and two distinct roots differ by a divisor of `f'(y)`.
- `PowerSeries.exists_X_pow_dvd_sub_map_of_C_mem_range`: if `ι(R)` contains the constants of a
  subfield `κ ⊆ K`, then every power series over `κ` is a `t`-adic limit of elements of `ι(R)`.
- `PowerSeries.liftOfCoeffMemRange`: the factorization of `ι` through `κ⟦t⟧` when all
  coefficients of `ι(R)` lie in `κ`.
- `PowerSeries.coeff_mem_range_of_algebraMap_mem_range`: a power series over `K` whose image in
  `Frac K⟦t⟧` comes from `Frac κ⟦t⟧` has coefficients in `κ`.

These are the inputs of the Hensel argument for the generic slice trait `S'` of SGA 4½,
[Th. finitude], 3.3–3.4: `Frac S'` is separably closed in `K((t))`.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] (ι : R →+* PowerSeries K) {π : R} (hπ : Irreducible π)
  (hιπ : ι π = PowerSeries.X)

include hπ hιπ in
/-- Divisibility by powers of the uniformizer is detected in `K⟦t⟧`. -/
lemma pow_dvd_of_X_pow_dvd {r : R} {n : ℕ} (h : (PowerSeries.X : PowerSeries K) ^ n ∣ ι r) :
    π ^ n ∣ r := by
  rcases eq_or_ne r 0 with rfl | hr
  · exact dvd_zero _
  obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible hr hπ
  rw [map_mul, map_pow, hιπ, (u.isUnit.map ι).dvd_mul_left] at h
  have hnm : n ≤ m := by
    by_contra! hlt
    simpa using PowerSeries.X_pow_dvd_iff.1 h m hlt
  exact (pow_dvd_pow π hnm).mul_left _

include hπ hιπ in
/-- An element of `R` whose image is `t ^ s` times a unit is `π ^ s` times a unit. -/
lemma exists_isUnit_eq_pow_mul_of_map [IsLocalHom ι] {r : R} {s : ℕ} {v : PowerSeries K}
    (hv : IsUnit v) (h : ι r = PowerSeries.X ^ s * v) : ∃ a, IsUnit a ∧ r = π ^ s * a := by
  obtain ⟨a, rfl⟩ := pow_dvd_of_X_pow_dvd ι hπ hιπ (r := r) (n := s) ⟨v, h⟩
  refine ⟨a, ?_, rfl⟩
  rw [map_mul, map_pow, hιπ] at h
  have : ι a = v := mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) h
  exact isUnit_of_map_unit ι a (this ▸ hv)

include hπ hιπ in
/-- **Simple roots in the closure of a henselian discrete valuation ring**: let `R` be henselian
with uniformizer `π`, `ι : R ⟶ K⟦t⟧` local with `ι π = t`. A simple root `y` of `f` (over `R`) in
`K⟦t⟧` which is a `t`-adic limit of elements of `ι(R)` lies in `ι(R)`. -/
theorem mem_range_of_isRoot_of_forall_exists_dvd [IsLocalHom ι] [HenselianLocalRing R] (f : R[X])
    {y : PowerSeries K} (hy : (f.map ι).IsRoot y) (hd : (f.map ι).derivative.eval y ≠ 0)
    (happrox : ∀ n : ℕ, ∃ z : R, (PowerSeries.X : PowerSeries K) ^ n ∣ ι z - y) :
    y ∈ ι.range := by
  set d := (f.map ι).derivative.eval y
  set s := d.order.toNat
  set u := PowerSeries.divXPowOrder d
  have hdu : PowerSeries.X ^ s * u = d := PowerSeries.X_pow_order_mul_divXPowOrder
  have hu0 : PowerSeries.constantCoeff u ≠ 0 :=
    fun h ↦ hd (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.1 h)
  obtain ⟨z, hz⟩ := happrox (2 * s + 1)
  have hfz : PowerSeries.X ^ (2 * s + 1) ∣ ι (f.eval z) := by
    rw [← eval_map_apply, ← sub_zero ((f.map ι).eval (ι z)), ← hy.eq_zero]
    exact hz.trans (sub_dvd_eval_sub _ _ _)
  have hf'z : PowerSeries.X ^ (2 * s + 1) ∣ ι (f.derivative.eval z) - d := by
    rw [← eval_map_apply, ← derivative_map]
    exact hz.trans (sub_dvd_eval_sub _ _ _)
  obtain ⟨w, hw⟩ := hf'z
  set v := u + PowerSeries.X ^ (s + 1) * w
  have hv : IsUnit v := by
    refine PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 ?_)
    simpa [v] using hu0
  have hιf' : ι (f.derivative.eval z) = PowerSeries.X ^ s * v := by
    rw [sub_eq_iff_eq_add] at hw
    rw [hw, ← hdu]
    ring
  obtain ⟨a, ha, hfa⟩ := exists_isUnit_eq_pow_mul_of_map ι hπ hιπ hv hιf'
  obtain ⟨w', hw'⟩ := pow_dvd_of_X_pow_dvd ι hπ hιπ hfz
  let c := π * w' * (↑ha.unit⁻¹ : R) ^ 2
  have hc : c ∈ maximalIdeal R :=
    Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ.not_isUnit)
  have hfc : f.eval z = (f.derivative.eval z) ^ 2 * c := by
    rw [hw', hfa]
    linear_combination (-(π ^ (2 * s + 1) * w') * (1 + a * (↑ha.unit⁻¹ : R))) * ha.mul_val_inv
  obtain ⟨b, hb, y', hy', hby⟩ := HenselianRing.exists_isRoot_of_eval_eq_sq_mul f z c hc hfc
  obtain ⟨y'', rfl⟩ : π ∣ y' := by rwa [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
  have hbz : PowerSeries.X ^ (s + 1) ∣ ι b - ι z := by
    rw [← map_sub, hby, map_mul, hιf', map_mul, hιπ]
    exact ⟨v * ι y'', by ring⟩
  have hb' : (f.map ι).IsRoot (ι b) := by
    rw [IsRoot, eval_map_apply, hb.eq_zero, map_zero]
  rcases Polynomial.eq_or_sub_dvd_derivative_eval_of_isRoot hy hb' with h | h
  · exact ⟨b, h.symm⟩
  · exfalso
    have h₁ : PowerSeries.X ^ (s + 1) ∣ y - ι b := by
      have : y - ι b = -(ι z - y) - (ι b - ι z) := by ring
      rw [this]
      exact dvd_sub (dvd_neg.2 ((pow_dvd_pow _ (by omega)).trans hz)) hbz
    have h₂ : PowerSeries.X ^ (s + 1) ∣ d := h₁.trans h
    rw [← hdu, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ PowerSeries.X_ne_zero)] at h₂
    exact hu0 (PowerSeries.X_dvd_iff.1 h₂)

end IsDiscreteValuationRing

namespace PowerSeries

variable {R : Type*} [CommRing R] {K : Type*} [Field K] {κ : Type*} [Field κ] [Algebra κ K]

/-- **Density**: let `ι : R ⟶ K⟦t⟧` with `ι π = t`. If the constants of `κ ⊆ K` lie in `ι(R)`,
every power series with coefficients in `κ` is a `t`-adic limit of elements of `ι(R)`. -/
lemma exists_X_pow_dvd_sub_map_of_C_mem_range (ι : R →+* PowerSeries K) {π : R}
    (hιπ : ι π = X) (h : ∀ a : κ, C (algebraMap κ K a) ∈ ι.range) (n : ℕ) (φ : PowerSeries κ) :
    ∃ z : R, (X : PowerSeries K) ^ n ∣ ι z - map (algebraMap κ K) φ := by
  induction n generalizing φ with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨z₁, hz₁⟩ := ih (mk fun p ↦ coeff (p + 1) φ)
    obtain ⟨r₀, hr₀⟩ := h (constantCoeff φ)
    refine ⟨r₀ + π * z₁, ?_⟩
    conv_rhs => rw [φ.eq_X_mul_shift_add_const]
    rw [map_add, map_mul, hr₀, hιπ, map_add, map_mul, map_X, map_C]
    convert mul_dvd_mul_left (X : PowerSeries K) hz₁ using 1
    · rw [pow_succ']
    · ring

/-- The factorization `R ⟶ κ⟦t⟧` of `ι : R ⟶ K⟦t⟧` when all coefficients of elements of `ι(R)`
lie in the subfield `κ ⊆ K`. -/
noncomputable def liftOfCoeffMemRange (ι : R →+* PowerSeries K)
    (h : ∀ r n, coeff n (ι r) ∈ (algebraMap κ K).range) : R →+* PowerSeries κ :=
  have hinj : Function.Injective (map (algebraMap κ K)) :=
    map_injective _ (algebraMap κ K).injective
  have hmem : ∀ r, ι r ∈ (map (algebraMap κ K)).range := fun r ↦
    ⟨mk fun n ↦ (h r n).choose, by ext n; simp [(h r n).choose_spec]⟩
  ((RingEquiv.ofLeftInverse (Function.leftInverse_invFun hinj)).symm.toRingHom).comp
    (ι.codRestrict _ hmem)

/-- `PowerSeries.liftOfCoeffMemRange ι h` is a factorization of `ι` through `κ⟦t⟧`. -/
@[simp]
lemma map_liftOfCoeffMemRange (ι : R →+* PowerSeries K)
    (h : ∀ r n, coeff n (ι r) ∈ (algebraMap κ K).range) (r : R) :
    map (algebraMap κ K) (liftOfCoeffMemRange ι h r) = ι r := by
  simp only [liftOfCoeffMemRange, RingHom.coe_comp, Function.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  exact congrArg Subtype.val ((RingEquiv.ofLeftInverse _).apply_symm_apply _)

/-- Let `j : Frac κ⟦t⟧ ⟶ Frac K⟦t⟧` extend the coefficientwise map. A power series over `K` whose
image in `Frac K⟦t⟧` lies in the image of `j` has coefficients in `κ`. -/
lemma coeff_mem_range_of_algebraMap_mem_range
    {j : FractionRing (PowerSeries κ) →+* FractionRing (PowerSeries K)}
    (hj : ∀ a, j (algebraMap _ _ a) = algebraMap _ _ (map (algebraMap κ K) a)) {φ : PowerSeries K}
    (h : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) φ ∈ j.range) (n : ℕ) :
    coeff n φ ∈ (algebraMap κ K).range := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := PowerSeries κ) w
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨u, hu, hbu⟩ : ∃ u, IsUnit u ∧ b = X ^ b.order.toNat * u :=
    ⟨divXPowOrder b, isUnit_iff_constantCoeff.2 (by
      rw [constantCoeff_divXPowOrder]
      exact (coeff_order hb0).isUnit), X_pow_order_mul_divXPowOrder.symm⟩
  have hinjK : Function.Injective (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) :=
    IsFractionRing.injective _ _
  have hbK : algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (map (algebraMap κ K) b) ≠ 0 :=
    (map_ne_zero_iff _ hinjK).2 ((map_ne_zero_iff _ (map_injective _ (algebraMap κ K).injective)).2
      hb0)
  rw [map_div₀, hj, hj, div_eq_iff hbK, ← map_mul] at hw
  have h₁ := hinjK hw
  rw [hbu, map_mul, map_pow, map_X] at h₁
  have h₂ : φ * X ^ b.order.toNat = map (algebraMap κ K) (a * ↑hu.unit⁻¹) := by
    have hu' : map (algebraMap κ K) u * map (algebraMap κ K) ↑hu.unit⁻¹ = 1 := by
      rw [← map_mul, hu.mul_val_inv, map_one]
    rw [map_mul]
    linear_combination -map (algebraMap κ K) ↑hu.unit⁻¹ * h₁ - φ * X ^ b.order.toNat * hu'
  have h₃ := congrArg (coeff (n + b.order.toNat)) h₂
  rw [coeff_mul_X_pow, coeff_map] at h₃
  exact ⟨_, h₃.symm⟩

end PowerSeries
