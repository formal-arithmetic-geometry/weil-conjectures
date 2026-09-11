/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular sequences over a local ring

Two consequences of Nakayama's lemma for a finite nonzero module `M` over a local ring `R` and an
ideal `I ≤ maximalIdeal R`: the submodule `I • M` is a proper submodule of `M`, and a single
element of the maximal ideal is an `M`-regular sequence of length one as soon as it is a
nonzerodivisor on `M`.
-/

@[expose] public section

open Pointwise RingTheory.Sequence

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Nakayama's lemma: an ideal contained in the maximal ideal of a local ring does not span a
finite nonzero module. -/
lemma Submodule.ideal_smul_top_lt_top [IsLocalRing R] [Nontrivial M] [Module.Finite R M]
    {I : Ideal R} (hI : I ≤ IsLocalRing.maximalIdeal R) : I • (⊤ : Submodule R M) < ⊤ :=
  lt_top_iff_ne_top.mpr (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (hI.trans (IsLocalRing.maximalIdeal_le_jacobson _))).symm

/-- Over a local ring, an element of the maximal ideal which is a nonzerodivisor on a finite
nonzero module `M` is an `M`-regular sequence of length one. -/
lemma IsLocalRing.isRegular_singleton_iff [IsLocalRing R] [Nontrivial M] [Module.Finite R M]
    {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) : IsRegular M [r] ↔ IsSMulRegular M r := by
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hr),
    isWeaklyRegular_singleton_iff]
