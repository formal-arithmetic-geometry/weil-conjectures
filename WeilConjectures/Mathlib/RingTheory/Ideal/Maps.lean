/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Two lemmas on ideals and ring homomorphisms

- `Ideal.exists_pow_mul_mem_of_algebraMap_mem_map`: clearing denominators, i.e. if the
  image of `x` in a localization away from `t` lies in the extension of an ideal `K`,
  then some power of `t` multiplies `x` into `K`;
- `Ideal.le_of_comap_le_comap_of_bijective`: an inclusion of ideals can be checked
  after pulling back along a bijective ring homomorphism.
-/

@[expose] public section

universe u

/-- **Clearing denominators in a localization**: if the image of `x` under the
localization map away from `t` lies in the extension of an ideal `K`, then some power
of `t` multiplies `x` into `K`. -/
lemma Ideal.exists_pow_mul_mem_of_algebraMap_mem_map {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] (t : R) [IsLocalization.Away t S] {K : Ideal R} {x : R}
    (hx : algebraMap R S x ∈ K.map (algebraMap R S)) :
    ∃ k : ℕ, t ^ k * x ∈ K := by
  obtain ⟨⟨j, u⟩, hju⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers t) S).mp hx
  obtain ⟨k₁, hk₁⟩ := u.2
  have hu : (u : R) = t ^ k₁ := hk₁.symm
  have h0 : algebraMap R S (x * t ^ k₁ - j) = 0 := by
    rwa [map_sub, map_mul, sub_eq_zero, ← hu]
  obtain ⟨⟨-, k₂, rfl⟩, hk₂⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers t) S _).mp h0
  refine ⟨k₂ + k₁, ?_⟩
  have h1 : t ^ (k₂ + k₁) * x = t ^ k₂ * (j : R) := by
    have h2 : t ^ k₂ * (x * t ^ k₁ - (j : R)) = 0 := hk₂
    rw [pow_add]
    linear_combination h2
  rw [h1]
  exact K.mul_mem_left _ j.2

/-- Comparing two ideals through the pullback along a bijective ring homomorphism. -/
lemma Ideal.le_of_comap_le_comap_of_bijective {R S : Type u} [CommRing R]
    [CommRing S] {f : R →+* S} (hf : Function.Bijective f) {P Q : Ideal S}
    (h : P.comap f ≤ Q.comap f) : P ≤ Q := by
  intro x hx
  obtain ⟨y, rfl⟩ := hf.2 x
  exact h (Ideal.mem_comap.mpr hx)
