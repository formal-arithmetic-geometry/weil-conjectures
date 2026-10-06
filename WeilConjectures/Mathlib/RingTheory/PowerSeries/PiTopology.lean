/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.PowerSeries.PiTopology
public import WeilConjectures.Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Locally finite products of power series

A family `(f j)` of power series is *locally finite* if for every `n` all but finitely many of
the `f j` are congruent to `1` modulo `X ^ (n + 1)`. Such a family is multipliable in the
product topology, and the coefficients of degree at most `n` of its product are those of a
finite partial product over any finite set containing the exceptional indices for `n`.

## Main statements

- `PowerSeries.WithPiTopology.hasProd_of_X_pow_dvd_sub_one`
- `PowerSeries.WithPiTopology.coeff_tprod_of_X_pow_dvd_sub_one`
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

namespace WithPiTopology

open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace R]

/-- A locally finite family of power series is multipliable: if `S n` is a finite set of
indices outside of which every `f j` is congruent to `1` modulo `X ^ (n + 1)`, then the product
of the family has, in degree `n`, the coefficient of the finite product over `S n`. -/
theorem hasProd_of_X_pow_dvd_sub_one {J : Type*} {f : J → R⟦X⟧} (S : ℕ → Finset J)
    (hS : ∀ n, ∀ j ∉ S n, X ^ (n + 1) ∣ f j - 1) :
    HasProd f (mk fun n ↦ coeff n (∏ j ∈ S n, f j)) := by
  classical
  rw [HasProd, tendsto_iff_coeff_tendsto]
  intro n
  rw [coeff_mk]
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [Filter.eventually_ge_atTop (S n)] with t ht
  have h := X_pow_dvd_prod_sub_prod_of_subset ht f (n + 1) fun j _ hj ↦ hS n j hj
  rw [X_pow_dvd_iff] at h
  exact sub_eq_zero.1 (by simpa using h n (Nat.lt_succ_self n))

variable [T2Space R]

/-- The coefficients of degree at most `n` of the product of a locally finite family of power
series are those of the finite product over any finite set `s` of indices outside of which all
factors are congruent to `1` modulo `X ^ (n + 1)`. -/
theorem coeff_tprod_of_X_pow_dvd_sub_one {J : Type*} {f : J → R⟦X⟧} (S : ℕ → Finset J)
    (hS : ∀ n, ∀ j ∉ S n, X ^ (n + 1) ∣ f j - 1) {n : ℕ} (s : Finset J)
    (hs : ∀ j ∉ s, X ^ (n + 1) ∣ f j - 1) {k : ℕ} (hk : k ≤ n) :
    coeff k (∏' j, f j) = coeff k (∏ j ∈ s, f j) := by
  classical
  rw [(hasProd_of_X_pow_dvd_sub_one S hS).tprod_eq, coeff_mk]
  have h₁ := X_pow_dvd_prod_sub_prod_of_subset (Finset.subset_union_left (s₂ := s)) f (k + 1)
    fun j hj hjS ↦ hS k j hjS
  have h₂ := X_pow_dvd_prod_sub_prod_of_subset (Finset.subset_union_right (s₁ := S k)) f (k + 1)
    fun j hj hjs ↦ (pow_dvd_pow X (by omega)).trans (hs j hjs)
  rw [X_pow_dvd_iff] at h₁ h₂
  have e₁ := sub_eq_zero.1 (by simpa using h₁ k (Nat.lt_succ_self k))
  have e₂ := sub_eq_zero.1 (by simpa using h₂ k (Nat.lt_succ_self k))
  rw [← e₁, e₂]

end WithPiTopology

end PowerSeries
