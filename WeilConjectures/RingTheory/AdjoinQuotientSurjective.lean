/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Surjectivity of a quotient killing the generators of an adjoin

We show that if an ideal of `Algebra.adjoin R s` contains every generator in `s`, then the
quotient by it is a quotient of `R`.

## References

* Stacks Project, Tag 0334, Step 5.
-/

@[expose] public section

universe u v

/-- If an ideal `q` of `Algebra.adjoin R s` contains every element of `s`, then the algebra map
`R → Algebra.adjoin R s ⧸ q` is surjective. -/
theorem adjoin_quotient_surjective (R : Type u) (K : Type v)
    [CommRing R] [CommRing K] [Algebra R K] (s : Set K)
    (q : Ideal (Algebra.adjoin R s))
    (hs : ∀ x (hx : x ∈ s), (⟨x, Algebra.subset_adjoin hx⟩ :
      Algebra.adjoin R s) ∈ q) :
    Function.Surjective (algebraMap R (Algebra.adjoin R s ⧸ q)) := by
  intro y
  obtain ⟨⟨y, hy⟩, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    exact ⟨0, by simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr (hs y hy)).symm⟩
  | algebraMap r => exact ⟨r, rfl⟩
  | add y z hy hz iy iz =>
    obtain ⟨a, ha⟩ := iy
    obtain ⟨b, hb⟩ := iz
    refine ⟨a + b, ?_⟩
    change _ = (Ideal.Quotient.mk q) (⟨y, hy⟩ + ⟨z, hz⟩)
    rw [map_add, map_add, ha, hb]
  | mul y z hy hz iy iz =>
    obtain ⟨a, ha⟩ := iy
    obtain ⟨b, hb⟩ := iz
    refine ⟨a * b, ?_⟩
    change _ = (Ideal.Quotient.mk q) (⟨y, hy⟩ * ⟨z, hz⟩)
    rw [map_mul, map_mul, ha, hb]

