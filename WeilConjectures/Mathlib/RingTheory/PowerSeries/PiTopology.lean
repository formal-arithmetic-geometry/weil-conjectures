/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

@[expose] public section

/-!
# Coefficientwise infinite products of power series

A family `f : ι → R⟦X⟧` whose members are congruent to `1` modulo increasing powers of
`X` is multipliable for the coefficientwise topology of `PowerSeries.WithPiTopology`, and
each coefficient of the infinite product is already reached by a finite subproduct. This
file makes both statements precise for a family of *orders* `d : ι → ℕ` with finite
bounded fibres, in the form

`X ^ d i ∣ f i - 1` for all `i`, and `{i | d i ≤ n}` finite for all `n`.

## Main results

- `PowerSeries.coeff_prod_congr`, factors congruent to `1` modulo `X ^ (n + 1)` do not
  affect the `n`-th coefficient of a finite product
- `PowerSeries.WithPiTopology.multipliable_of_X_pow_dvd_sub_one`
- `PowerSeries.WithPiTopology.coeff_tprod_eq_coeff_prod`
-/

open Filter

namespace PowerSeries

variable {R : Type*} [CommRing R] {ι : Type*} {f : ι → R⟦X⟧} {d : ι → ℕ}

/-- A finite product of power series congruent to `1` modulo `X ^ k` is congruent to `1`
modulo `X ^ k`. (blueprint: `lemma:weil-X-pow-dvd-prod-sub-one`) -/
theorem X_pow_dvd_prod_sub_one {k : ℕ} {S : Finset ι}
    (hf : ∀ i ∈ S, (X : R⟦X⟧) ^ k ∣ f i - 1) :
    (X : R⟦X⟧) ^ k ∣ (∏ i ∈ S, f i) - 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have h1 := hf a (Finset.mem_insert_self a S)
    have h2 := ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, show f a * ∏ i ∈ S, f i - 1 =
      f a * ((∏ i ∈ S, f i) - 1) + (f a - 1) by ring]
    exact dvd_add (h2.mul_left _) h1

/-- Multiplying by a power series congruent to `1` modulo `X ^ (n + 1)` does not change
the `n`-th coefficient. (blueprint: `lemma:weil-coeff-mul-eq-of-X-pow-dvd-sub-one`) -/
theorem coeff_mul_eq_of_X_pow_dvd_sub_one {F H : R⟦X⟧} {n : ℕ}
    (hH : (X : R⟦X⟧) ^ (n + 1) ∣ H - 1) : coeff n (H * F) = coeff n F := by
  obtain ⟨c, hc⟩ := hH
  have hH : H = X ^ (n + 1) * c + 1 := by rw [← hc]; ring
  rw [show H * F = X ^ (n + 1) * (c * F) + F by rw [hH]; ring, map_add, coeff_X_pow_mul',
    if_neg (by omega), zero_add]

/-- Factors congruent to `1` modulo `X ^ (n + 1)` do not affect the `n`-th coefficient of
a finite product. (blueprint: `lemma:weil-coeff-prod-congr`) -/
theorem coeff_prod_congr {S T : Finset ι} (hTS : T ⊆ S) {n : ℕ}
    (hf : ∀ i ∈ S, i ∉ T → (X : R⟦X⟧) ^ (n + 1) ∣ f i - 1) :
    coeff n (∏ i ∈ S, f i) = coeff n (∏ i ∈ T, f i) := by
  classical
  rw [← Finset.prod_sdiff hTS]
  exact coeff_mul_eq_of_X_pow_dvd_sub_one (X_pow_dvd_prod_sub_one fun i hi ↦
    hf i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2)

namespace WithPiTopology

open scoped WithPiTopology

variable [TopologicalSpace R]

/-- A family of power series congruent to `1` modulo `X ^ d i`, with only finitely many
orders `d i` below any given bound, is multipliable for the coefficientwise topology.
(blueprint: `lemma:weil-multipliable-of-X-pow-dvd-sub-one`) -/
theorem multipliable_of_X_pow_dvd_sub_one (hfin : ∀ n, {i | d i ≤ n}.Finite)
    (hf : ∀ i, (X : R⟦X⟧) ^ d i ∣ f i - 1) : Multipliable f := by
  classical
  have hsum : Summable fun s : Finset ι ↦ ∏ i ∈ s, (f i - 1) := by
    rw [summable_iff_summable_coeff]
    intro n
    refine summable_of_hasFiniteSupport ((hfin n).toFinset.powerset.finite_toSet.subset ?_)
    intro s hs
    rw [Function.mem_support] at hs
    rw [Finset.mem_coe, Finset.mem_powerset]
    intro j hj
    rw [Set.Finite.mem_toFinset]
    by_contra hjn
    rw [Set.mem_setOf_eq, not_le] at hjn
    exact hs (X_pow_dvd_iff.mp
      (((pow_dvd_pow (X : R⟦X⟧) hjn).trans (hf j)).trans
        (Finset.dvd_prod_of_mem (fun i ↦ f i - 1) hj)) n (Nat.lt_succ_self n))
  exact (multipliable_one_add_of_summable_prod hsum).congr fun i ↦ by ring

/-- The `n`-th coefficient of the infinite product `∏' i, f i` is already reached by the
finite subproduct over any finset containing every index of order at most `n`.
(blueprint: `lemma:weil-coeff-tprod-eq-coeff-prod`) -/
theorem coeff_tprod_eq_coeff_prod [T2Space R] (hfin : ∀ n, {i | d i ≤ n}.Finite)
    (hf : ∀ i, (X : R⟦X⟧) ^ d i ∣ f i - 1) (n : ℕ) {T : Finset ι}
    (hT : ∀ i, d i ≤ n → i ∈ T) :
    coeff n (∏' i, f i) = coeff n (∏ i ∈ T, f i) := by
  classical
  set T₀ : Finset ι := (hfin n).toFinset with hT₀
  have hlt : ∀ i, i ∉ T₀ → (X : R⟦X⟧) ^ (n + 1) ∣ f i - 1 := fun i hi ↦ by
    have hi' : n < d i := not_le.mp fun h ↦ hi ((hfin n).mem_toFinset.mpr h)
    exact (pow_dvd_pow (X : R⟦X⟧) (Nat.succ_le_of_lt hi')).trans (hf i)
  have htend : Tendsto (fun s : Finset ι ↦ coeff n (∏ i ∈ s, f i)) atTop
      (nhds (coeff n (∏' i, f i))) :=
    ((continuous_coeff R n).tendsto _).comp
      (multipliable_of_X_pow_dvd_sub_one hfin hf).hasProd
  have heq : Filter.EventuallyEq atTop (fun _ : Finset ι ↦ coeff n (∏ i ∈ T₀, f i))
      (fun s : Finset ι ↦ coeff n (∏ i ∈ s, f i)) := by
    filter_upwards [Filter.eventually_ge_atTop T₀] with s hs
    exact (coeff_prod_congr hs fun i _ hi ↦ hlt i hi).symm
  refine (tendsto_nhds_unique htend (Filter.Tendsto.congr' heq tendsto_const_nhds)).trans
    (coeff_prod_congr (fun i hi ↦ hT i ((hfin n).mem_toFinset.mp hi))
      fun i _ hi ↦ hlt i hi).symm

end WithPiTopology

end PowerSeries

end
