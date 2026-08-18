/-
Copyright (c) 2026 Tingxiao Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tingxiao Shi
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import WeilConjectures.Mathlib.Dynamics.PeriodicPts.Defs

@[expose] public section

/-!
# Counting the periodic points of a self-map by orbits

Let `f : α → α` be a self-map whose set of points of period `n` is finite. Every such point
lies on exactly one finite orbit, and an orbit of minimal period `m` consists of `m` points of
period `n` as soon as `m ∣ n`. Counting the points of period `n` orbit by orbit therefore gives
`N n = ∑_{m ∣ n} m * a m`, where `N n` is the number of points of period `n` and `a m` the
number of orbits of minimal period `m`. Möbius inversion recovers `a m` from `N`.

For a geometric Frobenius acting on the geometric points of a variety over a finite field,
`N n` is the number of `𝔽_{q^n}`-points and `a m` the number of closed points of degree `m`;
this is the combinatorial input to the Euler product for the zeta function.

## Main definitions

- `Function.orbitsOfMinimalPeriod` — the set of orbits of `f` of a given minimal period,
  as a set of cycles.
- `Function.orbitCount` — its cardinality `a m`.
- `Function.moebiusPtsOfPeriodSum` — the Möbius transform `∑_{r ∣ m} μ r * N (m / r)`.

## Main results

- `Function.ncard_ptsOfPeriod_eq_sum_divisors_mul_orbitCount` — `N n = ∑_{m ∣ n} m * a m`.
- `Function.moebiusPtsOfPeriodSum_eq_mul_orbitCount` — `∑_{r ∣ m} μ r * N (m / r) = m * a m`,
  whence the divisibility `Function.natCast_dvd_moebiusPtsOfPeriodSum` and the recovery
  formula `Function.moebiusPtsOfPeriodSum_div_natCast`.

## Implementation notes

Orbits are `Function.periodicOrbit f x : Cycle α`, so that the minimal period of a point is the
length of its orbit (`Function.periodicOrbit_length`). All counting is done with `Set.ncard`,
so that no decidability instance enters a definition; the finsets used in the proofs are
produced by `Set.Finite.toFinset` under `classical`.
-/

open Finset

namespace Function

variable {α : Type*} {f : α → α} {m n : ℕ}

/-- The set of orbits of `f` all of whose points have minimal period `m`. The restriction to
periodic points is automatic for `0 < m`; it is there to make the set empty at `m = 0`,
where `Function.periodicOrbit` takes the junk value `Cycle.nil`.
(blueprint: `def:weil-degree-frobenius-orbit-set`) -/
def orbitsOfMinimalPeriod (f : α → α) (m : ℕ) : Set (Cycle α) :=
  periodicOrbit f '' {x ∈ periodicPts f | minimalPeriod f x = m}

/-- The number of orbits of `f` of minimal period `m`.
(blueprint: `def:weil-frobenius-orbit-count`) -/
noncomputable def orbitCount (f : α → α) (m : ℕ) : ℕ :=
  (orbitsOfMinimalPeriod f m).ncard

/-- There is no orbit of degree zero. (blueprint: `lemma:weil-frobenius-orbit-count-zero`) -/
@[simp]
theorem orbitsOfMinimalPeriod_zero (f : α → α) : orbitsOfMinimalPeriod f 0 = ∅ := by
  refine Set.image_eq_empty.mpr (Set.eq_empty_of_forall_notMem fun x hx ↦ ?_)
  exact absurd hx.2 (minimalPeriod_pos_iff_mem_periodicPts.mpr hx.1).ne'

/-- There is no orbit of degree zero. (blueprint: `lemma:weil-frobenius-orbit-count-zero`) -/
@[simp]
theorem orbitCount_zero (f : α → α) : orbitCount f 0 = 0 := by
  rw [orbitCount, orbitsOfMinimalPeriod_zero, Set.ncard_empty]

/-- Counting the points of period `n` orbit by orbit: each orbit relevant at `n` is one of
minimal period `m` for some divisor `m` of `n`, and contributes exactly `m` points.
(blueprint: `prop:weil-fixed-points-orbit-count`) -/
theorem ncard_ptsOfPeriod_eq_sum_divisors_mul_orbitCount (hn : 0 < n)
    (hfin : (ptsOfPeriod f n).Finite) :
    (ptsOfPeriod f n).ncard = ∑ m ∈ n.divisors, m * orbitCount f m := by
  classical
  set S : Finset α := hfin.toFinset with hSdef
  have hmemS : ∀ {x : α}, x ∈ S ↔ IsPeriodicPt f n x := by
    intro x
    rw [hSdef, Set.Finite.mem_toFinset, mem_ptsOfPeriod]
  set T : Finset (Cycle α) := S.image (periodicOrbit f) with hTdef
  have hfiber : ∀ x ∈ S,
      #{y ∈ S | periodicOrbit f y = periodicOrbit f x} = minimalPeriod f x := by
    intro x hx
    have hxp : x ∈ periodicPts f := mem_periodicPts.mpr ⟨n, hn, hmemS.mp hx⟩
    have himg : {y ∈ S | periodicOrbit f y = periodicOrbit f x}
        = (Finset.range (minimalPeriod f x)).image fun j ↦ f^[j] x := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      refine ⟨fun hy ↦ mem_periodicOrbit_iff_exists_lt_minimalPeriod.mp
          ((periodicOrbit_eq_iff_mem_periodicOrbit hxp).mp hy.2), ?_⟩
      rintro ⟨j, -, rfl⟩
      exact ⟨hmemS.mpr ((hmemS.mp hx).apply_iterate j), periodicOrbit_apply_iterate_eq hxp j⟩
    rw [himg, Finset.card_image_of_injOn, Finset.card_range]
    exact fun a ha b hb hab ↦
      iterate_injOn_Iio_minimalPeriod (by simpa using ha) (by simpa using hb) hab
  have hlen : ∀ c ∈ T, c.length ∈ n.divisors := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    rw [periodicOrbit_length]
    exact Nat.mem_divisors.mpr ⟨(hmemS.mp hx).minimalPeriod_dvd, hn.ne'⟩
  have hcount : ∀ m ∈ n.divisors, #{c ∈ T | c.length = m} = orbitCount f m := by
    intro m hm
    rw [orbitCount, ← Set.ncard_coe_finset]
    congr 1
    ext c
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hTdef, Finset.mem_image,
      orbitsOfMinimalPeriod, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hc⟩
      rw [periodicOrbit_length] at hc
      exact ⟨x, ⟨mem_periodicPts.mpr ⟨n, hn, hmemS.mp hx⟩, hc⟩, rfl⟩
    · rintro ⟨x, ⟨-, hx⟩, rfl⟩
      refine ⟨⟨x, hmemS.mpr (isPeriodicPt_iff_minimalPeriod_dvd.mpr ?_), rfl⟩, ?_⟩
      · exact hx ▸ (Nat.mem_divisors.mp hm).1
      · rw [periodicOrbit_length, hx]
  have hScard : (ptsOfPeriod f n).ncard = #S := by
    rw [← Set.ncard_coe_finset, hSdef, Set.Finite.coe_toFinset]
  rw [hScard, Finset.card_eq_sum_card_fiberwise (t := T) fun x hx ↦ Finset.mem_image_of_mem _ hx,
    ← Finset.sum_fiberwise_of_maps_to hlen]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hconst : ∀ c ∈ {c ∈ T | c.length = m}, #{y ∈ S | periodicOrbit f y = c} = m := by
    intro c hc
    obtain ⟨hcT, hcm⟩ := Finset.mem_filter.mp hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hcT
    rw [hfiber x hx, ← periodicOrbit_length]
    exact hcm
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm, hcount m hm]

/-- The Möbius transform `∑_{r ∣ m} μ r * N (m / r)` of the function counting the points of
period `m` of `f`. (blueprint: `def:weil-orbit-count-mobius-numerator`) -/
noncomputable def moebiusPtsOfPeriodSum (f : α → α) (m : ℕ) : ℤ :=
  ∑ r ∈ m.divisors, ArithmeticFunction.moebius r * ((ptsOfPeriod f (m / r)).ncard : ℤ)

/-- Möbius inversion of `Function.ncard_ptsOfPeriod_eq_sum_divisors_mul_orbitCount`.
(blueprint: `lemma:weil-orbit-count-mobius-numerator-eq`) -/
theorem moebiusPtsOfPeriodSum_eq_mul_orbitCount (hm : 0 < m)
    (hfin : (ptsOfPeriod f m).Finite) :
    moebiusPtsOfPeriodSum f m = (m : ℤ) * orbitCount f m := by
  have hclosed : ∀ k l : ℕ, k ∣ l → l ∈ {k | k ∣ m} → k ∈ {k | k ∣ m} :=
    fun _ _ hkl hl ↦ hkl.trans hl
  have hsum : ∀ k : ℕ, 0 < k → k ∈ {k | k ∣ m} →
      ∑ i ∈ k.divisors, ((i : ℤ) * (orbitCount f i : ℤ))
        = ((ptsOfPeriod f k).ncard : ℤ) := by
    intro k hk hkm
    have := ncard_ptsOfPeriod_eq_sum_divisors_mul_orbitCount (f := f) hk
      (hfin.subset (ptsOfPeriod_subset_of_dvd f hkm))
    exact_mod_cast this.symm
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on (R := ℤ)
    (f := fun i ↦ (i : ℤ) * (orbitCount f i : ℤ))
    (g := fun k ↦ ((ptsOfPeriod f k).ncard : ℤ)) _ hclosed).mp hsum m hm dvd_rfl
  simp only [Int.cast_id] at key
  rw [moebiusPtsOfPeriodSum, ← Nat.sum_divisorsAntidiagonal
    fun r s ↦ ArithmeticFunction.moebius r * ((ptsOfPeriod f s).ncard : ℤ)]
  exact key

/-- The Möbius transform of the periodic-point counting function is divisible by the degree.
(blueprint: `cor:weil-orbit-count-mobius-integrality`) -/
theorem natCast_dvd_moebiusPtsOfPeriodSum (hm : 0 < m) (hfin : (ptsOfPeriod f m).Finite) :
    (m : ℤ) ∣ moebiusPtsOfPeriodSum f m :=
  ⟨(orbitCount f m : ℤ), moebiusPtsOfPeriodSum_eq_mul_orbitCount hm hfin⟩

/-- Möbius recovery of the orbit counts from the periodic-point counts.
(blueprint: `cor:weil-orbit-count-mobius-recovery`) -/
theorem moebiusPtsOfPeriodSum_div_natCast (hm : 0 < m) (hfin : (ptsOfPeriod f m).Finite) :
    moebiusPtsOfPeriodSum f m / (m : ℤ) = orbitCount f m := by
  rw [moebiusPtsOfPeriodSum_eq_mul_orbitCount hm hfin,
    Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr hm.ne')]

end Function
