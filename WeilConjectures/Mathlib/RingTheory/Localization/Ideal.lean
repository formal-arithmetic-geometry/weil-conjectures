/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Colon ideals and localization

Colon ideals commute with localization when the second ideal is finitely generated
(`Ideal.map_colon_of_isLocalization`).
-/

@[expose] public section

/-- **Colon ideals commute with localization** when the second ideal is finitely generated. -/
lemma Ideal.map_colon_of_isLocalization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (I J : Ideal A) (hJ : J.FG) :
    (I.colon (J : Set A)).map (algebraMap A B) =
      (I.map (algebraMap A B)).colon (J.map (algebraMap A B) : Set B) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Submodule.mem_colon]
    intro s hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      rw [smul_eq_mul, ← map_mul]
      exact Ideal.mem_map_of_mem _ (Submodule.mem_colon.mp ha j hj)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Ideal.mul_mem_left _ c hx
  · intro b hb
    obtain ⟨t, rfl⟩ := hJ
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M b
    have h (j : A) (hj : j ∈ t) : ∃ m ∈ M, m * (a * j) ∈ I := by
      rw [← IsLocalization.mk'_mem_map_algebraMap_iff M B I (a * j) s,
        IsLocalization.mk'_eq_mul_mk'_one,
        mul_comm a j, map_mul, mul_assoc, ← IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
      exact Submodule.mem_colon.mp hb _ (Ideal.mem_map_of_mem _ (Ideal.subset_span hj))
    choose! m hmM hm using h
    rw [IsLocalization.mk'_mem_map_algebraMap_iff M B]
    refine ⟨∏ j ∈ t, m j, Submonoid.prod_mem M fun j hj ↦ hmM j hj, ?_⟩
    rw [Submodule.mem_colon]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      classical
      have e : (∏ j ∈ t, m j) * a * x = (∏ j ∈ t.erase x, m j) * (m x * (a * x)) := by
        rw [← Finset.mul_prod_erase t m hx]
        ring
      rw [smul_eq_mul, e]
      exact Ideal.mul_mem_left _ _ (hm x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul c x _ hx => rw [smul_comm]; exact Ideal.mul_mem_left _ c hx
