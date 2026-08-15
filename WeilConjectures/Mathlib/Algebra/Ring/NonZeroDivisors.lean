/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Nonzerodivisors under bijective ring homomorphisms

Bijective ring homomorphisms map nonzerodivisors to nonzerodivisors.
-/

@[expose] public section

universe u v

/-- Nonzerodivisors map to nonzerodivisors under bijective ring homomorphisms. -/
lemma map_mem_nonZeroDivisors_of_bijective {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Bijective f) {c : A} (hc : c ∈ nonZeroDivisors A) :
    f c ∈ nonZeroDivisors B := by
  rw [mem_nonZeroDivisors_iff] at hc ⊢
  refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩ <;> obtain ⟨z, rfl⟩ := hf.2 z
  · have h0 : c * z = 0 := hf.1 (by rw [map_mul, map_zero]; exact hz)
    rw [hc.1 z h0, map_zero]
  · have h0 : z * c = 0 := hf.1 (by rw [map_mul, map_zero]; exact hz)
    rw [hc.2 z h0, map_zero]
