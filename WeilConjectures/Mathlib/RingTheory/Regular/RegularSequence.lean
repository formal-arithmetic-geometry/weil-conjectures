/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular sequences over a local ring

Three consequences of Nakayama's lemma for a finite nonzero module `M` over a local ring `R` and
an ideal `I ≤ maximalIdeal R`: the submodule `I • M` is a proper submodule of `M`; a generator of
`M`, when `M` is cyclic, stays a generator of the fibre `M / 𝔪 M`, so that `r • m ∈ 𝔪 M` forces
`r ∈ 𝔪`; and a single element of the maximal ideal is an `M`-regular sequence of length one as
soon as it is a nonzerodivisor on `M`.
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

/-- **A generator of a cyclic module over a local ring generates the fibre.** If a single
element `m` spans a nonzero module `M` over a local ring `R`, then `r • m` lies in `𝔪 M`
exactly when `r` lies in `𝔪`.

Finiteness of `M` is not assumed: it follows from `hm`. -/
theorem Submodule.smul_mem_maximalIdeal_smul_top_iff [IsLocalRing R] [Nontrivial M] {m : M}
    (hm : Submodule.span R {m} = ⊤) (r : R) :
    r • m ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔
      r ∈ IsLocalRing.maximalIdeal R := by
  have : Module.Finite R M := ⟨hm ▸ Submodule.fg_span_singleton _⟩
  refine ⟨fun h ↦ ?_, fun h ↦ Submodule.smul_mem_smul h Submodule.mem_top⟩
  by_contra hr
  -- were `r` a unit, the generator `m` would lie in `𝔪 M`, hence so would all of `M`
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
  obtain ⟨u, rfl⟩ := hr
  have hmem := Submodule.smul_mem (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))
    ((u⁻¹ : Rˣ) : R) h
  rw [smul_smul, Units.inv_mul, one_smul] at hmem
  have hle : Submodule.span R {m} ≤ IsLocalRing.maximalIdeal R • ⊤ :=
    Submodule.span_le.2 (Set.singleton_subset_iff.2 hmem)
  rw [hm] at hle
  exact absurd (le_antisymm le_top hle) (Submodule.ideal_smul_top_lt_top le_rfl).ne

/-- Over a local ring, an element of the maximal ideal which is a nonzerodivisor on a finite
nonzero module `M` is an `M`-regular sequence of length one. -/
lemma IsLocalRing.isRegular_singleton_iff [IsLocalRing R] [Nontrivial M] [Module.Finite R M]
    {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) : IsRegular M [r] ↔ IsSMulRegular M r := by
  rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hr),
    isWeaklyRegular_singleton_iff]
