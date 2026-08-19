/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import WeilConjectures.EulerProductAux
public import WeilConjectures.ZetaCounting.Defs

@[expose] public section

/-!
# Euler products for the zeta series of a counting function

Let `d : ι → ℕ` be a family of positive degrees with only finitely many members below any
given bound, and let `c : ℕ → ℕ` count, at every `n ≥ 1`, the degrees dividing `n` with
multiplicity: `c n = ∑_{d i ∣ n} d i`. The zeta series of `c` is then the Euler product

`Z_c = ∏' i, (1 - X ^ d i)⁻¹`,

and grouping the factors of equal degree turns this into `∏' m, ((1 - X ^ m)⁻¹) ^ a m`,
where `a m` is the number of indices of degree `m`. Both products converge
coefficientwise, i.e. in `PowerSeries.WithPiTopology`.

Since the factors `(1 - X ^ m)⁻¹` have coefficients `0` and `1`, the Euler product also
exhibits `Z_c` as the image of a power series with integer coefficients.

## Main results

- `PowerSeries.countingZetaSeries_eq_tprod`, the Euler product of a degree family
- `PowerSeries.countingZetaSeries_eq_tprod_pow`, the same product grouped by degree,
  stated directly in terms of the multiplicity function `a`
- `PowerSeries.exists_map_intCast_eq_countingZetaSeries`, the integral lift; the
  coefficientwise form is `PowerSeries.coeff_countingZetaSeries_mem_range`

## Implementation notes

The intended downstream interface is `countingZetaSeries_eq_tprod`: it takes exactly the
data a geometric situation provides, namely a degree function together with the point
counting formula, and it specialises to the classical Euler product over closed points
(`WeilConjectures.ZetaCounting.Comparison`) and to the orbit form of a self-map
(`WeilConjectures.ZetaCounting.Orbits`).
-/

namespace PowerSeries

noncomputable section

variable {ι : Type*} {d : ι → ℕ} {c : ℕ → ℕ}

open scoped WithPiTopology in
/-- **The Euler product for the zeta series of a counting function.** If `d : ι → ℕ` is a
family of positive degrees with finitely many members below any bound, and if the counting
function `c` satisfies `c n = ∑_{d i ∣ n} d i` for every `n ≥ 1`, then the zeta series of
`c` is the Euler product `∏' i, (1 - X ^ d i)⁻¹`.
(blueprint: `thm:weil-counting-zeta-euler-product`) -/
theorem countingZetaSeries_eq_tprod (hd : ∀ i, d i ≠ 0) (hfin : ∀ n, {i | d i ≤ n}.Finite)
    (hc : ∀ n, n ≠ 0 → ∀ T : Finset ι, (∀ i, d i ∣ n → i ∈ T) →
      c n = ∑ i ∈ T with d i ∣ n, d i) :
    countingZetaSeries c = ∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧) := by
  classical
  ext n
  set T : Finset ι := (hfin n).toFinset with hT_def
  have hT : ∀ i, d i ≤ n → i ∈ T := fun i hi ↦ by simpa [hT_def] using hi
  rw [coeff_tprod_inv_one_sub_X_pow hd hfin n hT]
  refine coeff_eq_of_X_mul_derivative_eq (X_mul_derivative_countingZetaSeries c)
    (X_mul_derivative_prod_inv_one_sub_X_pow _ T fun i _ ↦ hd i) ?_ (by simp) ?_ n le_rfl
  · rw [constantCoeff_countingZetaSeries, map_prod]
    exact (Finset.prod_eq_one fun i _ ↦ constantCoeff_inv_one_sub_X_pow (hd i)).symm
  · intro i hi
    rcases eq_or_ne i 0 with rfl | hi0
    · simp
    · rw [coeff_mk, if_neg hi0, map_sum]
      simp only [coeff_mk]
      rw [hc i hi0 T fun x hx ↦ hT x ((Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hx).trans hi),
        Finset.sum_filter, Nat.cast_sum]
      exact Finset.sum_congr rfl fun x _ ↦ by simp [hi0]

/-! ### Grouping the Euler factors by degree -/

private lemma X_pow_dvd_pow_inv_one_sub_X_pow_sub_one (a : ℕ → ℕ) (m : ℕ) :
    (X : ℚ⟦X⟧) ^ m ∣ ((1 - X ^ m)⁻¹ : ℚ⟦X⟧) ^ a m - 1 := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · exact dvd_trans ⟨((1 - X ^ m)⁻¹ : ℚ⟦X⟧), inv_one_sub_X_pow_sub_one hm⟩
      (by simpa using sub_dvd_pow_sub_pow ((1 - X ^ m)⁻¹ : ℚ⟦X⟧) 1 (a m))

open WithPiTopology in
/-- **The degree-grouped Euler product.** If the counting function `c` is obtained from a
multiplicity function `a` by `c n = ∑_{m ∣ n} m * a m`, then the zeta series of `c` is the
product of the `a m`-th powers of the geometric series `(1 - X ^ m)⁻¹`. Degree `0` must
not occur, so `a 0 = 0` is required.
(blueprint: `thm:weil-counting-zeta-degree-euler-product`) -/
theorem countingZetaSeries_eq_tprod_pow {a : ℕ → ℕ} (ha : a 0 = 0)
    (hc : ∀ n, n ≠ 0 → c n = ∑ m ∈ n.divisors, m * a m) :
    countingZetaSeries c = ∏' m : ℕ, ((1 - X ^ m)⁻¹ : ℚ⟦X⟧) ^ a m := by
  classical
  ext n
  rw [coeff_tprod_eq_coeff_prod (d := id) (fun k ↦ Set.finite_Iic k)
    (X_pow_dvd_pow_inv_one_sub_X_pow_sub_one a) n
    (T := Finset.range (n + 1)) fun m hm ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le hm)]
  set S : Finset ((_ : ℕ) × ℕ) := (Finset.range (n + 1)).sigma fun m ↦ Finset.range (a m)
    with hS
  have hmem : ∀ p ∈ S, p.1 ≠ 0 := by
    rintro ⟨m, j⟩ hp rfl
    rw [hS, Finset.mem_sigma, ha] at hp
    simp at hp
  have hprod : ∏ m ∈ Finset.range (n + 1), ((1 - X ^ m)⁻¹ : ℚ⟦X⟧) ^ a m =
      ∏ p ∈ S, ((1 - X ^ p.1)⁻¹ : ℚ⟦X⟧) := by
    rw [hS, Finset.prod_sigma]
    exact Finset.prod_congr rfl fun m _ ↦ by simp
  rw [hprod]
  refine coeff_eq_of_X_mul_derivative_eq (X_mul_derivative_countingZetaSeries c)
    (X_mul_derivative_prod_inv_one_sub_X_pow _ S hmem) ?_ (by simp) ?_ n le_rfl
  · rw [constantCoeff_countingZetaSeries, map_prod]
    exact (Finset.prod_eq_one fun p hp ↦ constantCoeff_inv_one_sub_X_pow (hmem p hp)).symm
  · intro i hi
    rcases eq_or_ne i 0 with rfl | hi0
    · simp
    · rw [coeff_mk, if_neg hi0, map_sum]
      simp only [coeff_mk]
      rw [hS, hc i hi0, Nat.cast_sum, Finset.sum_sigma]
      refine (Finset.sum_congr rfl fun m hm ↦ ?_).trans (Finset.sum_subset ?_ ?_)
      · have hdvd : m ∣ i ∧ i ≠ 0 := ⟨Nat.dvd_of_mem_divisors hm, hi0⟩
        simp only [Finset.sum_const, Finset.card_range, if_pos hdvd, nsmul_eq_mul]
        push_cast
        ring
      · intro m hm
        exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le ((Nat.le_of_dvd (Nat.pos_of_ne_zero hi0)
            (Nat.dvd_of_mem_divisors hm)).trans hi))
      · intro m _ hm
        have hdvd : ¬(m ∣ i ∧ i ≠ 0) := fun h ↦ hm (Nat.mem_divisors.mpr ⟨h.1, hi0⟩)
        simp only [Finset.sum_const, if_neg hdvd, smul_zero]

/-! ### From a degree family to its multiplicity function -/

/-- The counting hypothesis of `PowerSeries.countingZetaSeries_eq_tprod` implies the one
of `PowerSeries.countingZetaSeries_eq_tprod_pow` for the multiplicity function counting
the indices of each degree. (blueprint: `lemma:weil-degree-sum-eq-multiplicity-sum`) -/
theorem sum_filter_dvd_eq_sum_divisors_mul_ncard {n : ℕ} (hn : n ≠ 0) {T : Finset ι}
    (hT : ∀ i, d i ∣ n → i ∈ T) :
    ∑ i ∈ T with d i ∣ n, d i = ∑ m ∈ n.divisors, m * (d ⁻¹' {m}).ncard := by
  have hmaps : ∀ i ∈ T.filter fun i ↦ d i ∣ n, d i ∈ n.divisors := fun i hi ↦
    Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hi).2, hn⟩
  refine (Finset.sum_fiberwise_of_maps_to hmaps d).symm.trans
    (Finset.sum_congr rfl fun m hm ↦ ?_)
  have hdvd : m ∣ n := Nat.dvd_of_mem_divisors hm
  have hcoe : (↑((T.filter fun i ↦ d i ∣ n).filter fun i ↦ d i = m) : Set ι) = d ⁻¹' {m} := by
    ext i
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff,
      Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨hT i (h ▸ hdvd), h ▸ hdvd⟩, h⟩⟩
  rw [Finset.sum_congr rfl fun i hi ↦ (Finset.mem_filter.mp hi).2, Finset.sum_const,
    smul_eq_mul, ← Set.ncard_coe_finset, hcoe, mul_comm]

/-! ### Integrality -/

/-- A power series over `S` all of whose coefficients lie in the image of a ring
homomorphism `φ : R →+* S` is the image of a power series over `R`.
(blueprint: `lemma:weil-exists-map-eq-of-coeff-mem-range`) -/
theorem exists_map_eq_of_forall_coeff_mem_range {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {P : S⟦X⟧} (h : ∀ n, coeff n P ∈ φ.range) :
    ∃ Q : R⟦X⟧, map φ Q = P := by
  choose z hz using h
  exact ⟨mk z, by ext n; rw [coeff_map, coeff_mk, hz]⟩

open scoped WithPiTopology in
/-- The geometric series `(1 - X ^ d)⁻¹` have coefficients `0` and `1`, so every
coefficient of an Euler product is an integer.
(blueprint: `lemma:weil-coeff-tprod-mem-range`) -/
theorem coeff_tprod_inv_one_sub_X_pow_mem_range (hd : ∀ i, d i ≠ 0)
    (hfin : ∀ n, {i | d i ≤ n}.Finite) (n : ℕ) :
    coeff n (∏' i, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧)) ∈ (Int.castRingHom ℚ).range := by
  classical
  rw [coeff_tprod_inv_one_sub_X_pow hd hfin n
      (T := (hfin n).toFinset) fun i hi ↦ (hfin n).mem_toFinset.mpr hi,
    show ∏ i ∈ (hfin n).toFinset, ((1 - X ^ d i)⁻¹ : ℚ⟦X⟧) =
      map (Int.castRingHom ℚ)
        (∏ i ∈ (hfin n).toFinset, mk fun j ↦ if d i ∣ j then (1 : ℤ) else 0) from by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [inv_one_sub_X_pow_eq_mk (hd i)]
      ext j
      simp,
    coeff_map]
  exact ⟨_, rfl⟩

open scoped WithPiTopology in
/-- **Integrality of the zeta series.** Under the hypotheses of
`PowerSeries.countingZetaSeries_eq_tprod` every coefficient of the zeta series is an
integer. (blueprint: `cor:weil-counting-zeta-integral`) -/
theorem coeff_countingZetaSeries_mem_range (hd : ∀ i, d i ≠ 0)
    (hfin : ∀ n, {i | d i ≤ n}.Finite)
    (hc : ∀ n, n ≠ 0 → ∀ T : Finset ι, (∀ i, d i ∣ n → i ∈ T) →
      c n = ∑ i ∈ T with d i ∣ n, d i) (n : ℕ) :
    coeff n (countingZetaSeries c) ∈ (Int.castRingHom ℚ).range := by
  rw [countingZetaSeries_eq_tprod hd hfin hc]
  exact coeff_tprod_inv_one_sub_X_pow_mem_range hd hfin n

open WithPiTopology in
/-- Every coefficient of a degree-grouped Euler product is an integer.
(blueprint: `lemma:weil-coeff-tprod-pow-mem-range`) -/
theorem coeff_tprod_pow_inv_one_sub_X_pow_mem_range {a : ℕ → ℕ} (ha : a 0 = 0) (n : ℕ) :
    coeff n (∏' m : ℕ, ((1 - X ^ m)⁻¹ : ℚ⟦X⟧) ^ a m) ∈ (Int.castRingHom ℚ).range := by
  rw [coeff_tprod_eq_coeff_prod (d := id) (fun k ↦ Set.finite_Iic k)
      (X_pow_dvd_pow_inv_one_sub_X_pow_sub_one a) n
      (T := Finset.range (n + 1)) fun m hm ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le hm),
    show ∏ m ∈ Finset.range (n + 1), ((1 - X ^ m)⁻¹ : ℚ⟦X⟧) ^ a m =
      map (Int.castRingHom ℚ)
        (∏ m ∈ Finset.range (n + 1), (mk fun j ↦ if m ∣ j then (1 : ℤ) else 0) ^ a m) from by
      rw [map_prod]
      refine Finset.prod_congr rfl fun m _ ↦ ?_
      rcases eq_or_ne m 0 with rfl | hm
      · rw [ha, pow_zero, pow_zero, map_one]
      · rw [map_pow, inv_one_sub_X_pow_eq_mk hm]
        congr 1
        ext j
        simp,
    coeff_map]
  exact ⟨_, rfl⟩

/-- **Integrality of the degree-grouped zeta series.** Under the hypotheses of
`PowerSeries.countingZetaSeries_eq_tprod_pow` every coefficient of the zeta series is an
integer. (blueprint: `cor:weil-counting-zeta-integral-grouped`) -/
theorem coeff_countingZetaSeries_mem_range_of_multiplicity {a : ℕ → ℕ} (ha : a 0 = 0)
    (hc : ∀ n, n ≠ 0 → c n = ∑ m ∈ n.divisors, m * a m) (n : ℕ) :
    coeff n (countingZetaSeries c) ∈ (Int.castRingHom ℚ).range := by
  rw [countingZetaSeries_eq_tprod_pow ha hc]
  exact coeff_tprod_pow_inv_one_sub_X_pow_mem_range ha n

/-- **The integral lift of the zeta series.** Under the hypotheses of
`PowerSeries.countingZetaSeries_eq_tprod` the zeta series is the image of a power series
with integer coefficients. (blueprint: `thm:weil-counting-zeta-integral-lift`) -/
theorem exists_map_intCast_eq_countingZetaSeries (hd : ∀ i, d i ≠ 0)
    (hfin : ∀ n, {i | d i ≤ n}.Finite)
    (hc : ∀ n, n ≠ 0 → ∀ T : Finset ι, (∀ i, d i ∣ n → i ∈ T) →
      c n = ∑ i ∈ T with d i ∣ n, d i) :
    ∃ Z : ℤ⟦X⟧, map (Int.castRingHom ℚ) Z = countingZetaSeries c :=
  exists_map_eq_of_forall_coeff_mem_range _ (coeff_countingZetaSeries_mem_range hd hfin hc)

end

end PowerSeries

end
