/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.HenselianNonMonic
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisHensel
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Order

/-!

# Simple roots in the closure of a henselian discrete valuation ring in `K⟦t⟧`

Let `R` be a henselian discrete valuation ring with a uniformizer `π` and `ι : R ⟶ K⟦t⟧` a local
injection with `ι π = t`. A simple root `y ∈ K⟦t⟧` of a polynomial `f` over `R` which is a
`t`-adic limit of elements of `ι(R)` lies in `ι(R)`
(`IsDiscreteValuationRing.mem_range_of_isRoot_of_forall_exists_dvd`): with `s` the order of
`f'(y)`, an approximation `z` of `y` modulo `t^{2s+1}` satisfies `f(z) = f'(z)² c` with `c ∈ 𝔪`,
so Newton's lemma (`HenselianLocalRing.exists_isRoot_of_eval_eq_sq_mul`) gives a root `b` of `f`
with `ι b ≡ y (mod t^{s+1})`, and two distinct roots differ by a divisor of `f'(y)`.

This is the Hensel argument for the generic slice trait `S'` of SGA 4½, [Th. finitude], 3.3–3.4:
`Frac S'` is separably closed in its `t`-adic closure in `K((t))`.

-/

@[expose] public section

open Polynomial PowerSeries IsLocalRing

namespace IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] (ι : R →+* PowerSeries K) [IsLocalHom ι] {π : R} (hπ : Irreducible π)
  (hιπ : ι π = PowerSeries.X)

omit [IsLocalHom ι] in
include hπ hιπ in
/-- Divisibility by powers of the uniformizer is detected in `K⟦t⟧`. -/
lemma pow_dvd_of_X_pow_dvd_map {r : R} {n : ℕ} (h : (PowerSeries.X : PowerSeries K) ^ n ∣ ι r) :
    π ^ n ∣ r := by
  rcases eq_or_ne r 0 with rfl | hr
  · exact dvd_zero _
  obtain ⟨m, u, rfl⟩ := eq_unit_mul_pow_irreducible hr hπ
  rw [map_mul, map_pow, hιπ] at h
  have hu : IsUnit (ι u) := u.isUnit.map ι
  have h' : (PowerSeries.X : PowerSeries K) ^ n ∣ PowerSeries.X ^ m :=
    (hu.dvd_mul_left).1 h
  have hnm : n ≤ m := by
    by_contra hlt
    have := PowerSeries.X_pow_dvd_iff.1 h' m (by omega)
    simp at this
  exact Dvd.dvd.mul_left (pow_dvd_pow π hnm) _

include hπ hιπ in
/-- An element of `R` whose image is `t ^ s` times a unit is `π ^ s` times a unit. -/
lemma exists_isUnit_eq_pow_mul_of_map {r : R} {s : ℕ} {v : PowerSeries K} (hv : IsUnit v)
    (h : ι r = PowerSeries.X ^ s * v) : ∃ a, IsUnit a ∧ r = π ^ s * a := by
  obtain ⟨a, rfl⟩ := pow_dvd_of_X_pow_dvd_map ι hπ hιπ (r := r) (n := s) ⟨v, h⟩
  refine ⟨a, ?_, rfl⟩
  rw [map_mul, map_pow, hιπ] at h
  have : ι a = v := mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) h
  exact isUnit_of_map_unit ι a (this ▸ hv)

include hπ hιπ in
/-- **Simple roots in the closure of a henselian discrete valuation ring**: let `R` be henselian
with uniformizer `π`, `ι : R ⟶ K⟦t⟧` local with `ι π = t`. A simple root `y` of `f` (over `R`) in
`K⟦t⟧` which is a `t`-adic limit of elements of `ι(R)` lies in `ι(R)`. -/
theorem mem_range_of_isRoot_of_forall_exists_dvd [HenselianLocalRing R] (f : R[X])
    {y : PowerSeries K} (hy : (f.map ι).IsRoot y) (hd : (f.map ι).derivative.eval y ≠ 0)
    (happrox : ∀ n : ℕ, ∃ z : R, (PowerSeries.X : PowerSeries K) ^ n ∣ ι z - y) :
    y ∈ ι.range := by
  set d := (f.map ι).derivative.eval y
  set s := d.order.toNat
  set u := PowerSeries.divXPowOrder d
  have hdu : PowerSeries.X ^ s * u = d := PowerSeries.X_pow_order_mul_divXPowOrder
  have hu0 : PowerSeries.constantCoeff u ≠ 0 :=
    fun h ↦ hd (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.1 h)
  have hu : IsUnit u := PowerSeries.isUnit_iff_constantCoeff.2 (isUnit_iff_ne_zero.2 hu0)
  have hmap : ∀ (g : R[X]) (r : R), (g.map ι).eval (ι r) = ι (g.eval r) := fun g r ↦ by
    rw [eval_map, eval₂_hom]
  obtain ⟨z, hz⟩ := happrox (2 * s + 1)
  have hfz : PowerSeries.X ^ (2 * s + 1) ∣ ι (f.eval z) := by
    rw [← hmap, ← sub_zero ((f.map ι).eval (ι z)), ← hy.eq_zero]
    exact hz.trans (sub_dvd_eval_sub _ _ _)
  have hf'z : PowerSeries.X ^ (2 * s + 1) ∣ ι (f.derivative.eval z) - d := by
    rw [← hmap, ← derivative_map]
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
  obtain ⟨w', hw'⟩ := pow_dvd_of_X_pow_dvd_map ι hπ hιπ hfz
  have hπm : π ∈ maximalIdeal R := hπ.not_isUnit
  let c := π * w' * (↑ha.unit⁻¹ : R) ^ 2
  have hc : c ∈ maximalIdeal R := Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπm)
  have hfc : f.eval z = (f.derivative.eval z) ^ 2 * c := by
    rw [hw', hfa]
    have : a * (↑ha.unit⁻¹ : R) = 1 := ha.mul_val_inv
    calc π ^ (2 * s + 1) * w' = π ^ (2 * s + 1) * w' * (a * (↑ha.unit⁻¹ : R)) ^ 2 := by
          rw [this, one_pow, mul_one]
      _ = (π ^ s * a) ^ 2 * c := by ring
  obtain ⟨b, hb, y', hy', hby⟩ := HenselianLocalRing.exists_isRoot_of_eval_eq_sq_mul f z c hc hfc
  have hπy' : π ∣ y' := by
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
    exact hy'
  obtain ⟨y'', rfl⟩ := hπy'
  have hbz : PowerSeries.X ^ (s + 1) ∣ ι b - ι z := by
    rw [← map_sub, hby, map_mul, hιf', map_mul, hιπ]
    exact ⟨v * ι y'', by ring⟩
  have hb' : (f.map ι).IsRoot (ι b) := by
    rw [IsRoot, hmap, hb.eq_zero, map_zero]
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
