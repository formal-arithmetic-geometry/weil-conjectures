/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Relevance of the points of the projective spectrum

Every point of `ProjectiveSpectrum 𝒜` is a relevant homogeneous prime ideal, so it misses some
homogeneous element of positive degree (`ProjectiveSpectrum.exists_homogeneous_notMem`), and
hence homogeneous elements of arbitrarily large degree
(`ProjectiveSpectrum.exists_homogeneous_notMem_of_le`).

## TODO

When upstreaming, the `local_affine` field of `AlgebraicGeometry.Proj` in
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean` repeats the proof of
`ProjectiveSpectrum.exists_homogeneous_notMem` inline and should use it instead.
-/

@[expose] public section

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

namespace ProjectiveSpectrum

/-- Every point of `ProjectiveSpectrum 𝒜` is a relevant homogeneous prime ideal, hence misses
some homogeneous element of positive degree. -/
theorem exists_homogeneous_notMem (x : ProjectiveSpectrum 𝒜) :
    ∃ m > 0, ∃ f ∈ 𝒜 m, f ∉ x.asHomogeneousIdeal := by
  classical
  by_contra! h
  refine x.not_irrelevant_le fun z hz ↦ ?_
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  exact x.1.toIdeal.sum_mem fun k hk ↦
    h k (Nat.pos_of_ne_zero <| by aesop) _ (SetLike.coe_mem _)

/-- Every point of `ProjectiveSpectrum 𝒜` misses homogeneous elements of arbitrarily large
degree. -/
theorem exists_homogeneous_notMem_of_le (x : ProjectiveSpectrum 𝒜) (n : ℕ) :
    ∃ m ≥ n, ∃ f ∈ 𝒜 m, f ∉ x.asHomogeneousIdeal := by
  obtain ⟨d, hd, f, hf, hfx⟩ := x.exists_homogeneous_notMem
  refine ⟨n * d, Nat.le_mul_of_pos_right n hd, f ^ n,
    (by simpa [mul_comm] using SetLike.pow_mem_graded n hf),
    fun h ↦ hfx (x.isPrime.mem_of_pow_mem _ h)⟩

end ProjectiveSpectrum
