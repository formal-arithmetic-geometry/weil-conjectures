/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Relevance of the points of the projective spectrum
-/

@[expose] public section

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Every point of `ProjectiveSpectrum 𝒜` is a relevant homogeneous prime ideal, hence misses
some homogeneous element of positive degree. -/
theorem ProjectiveSpectrum.exists_homogeneous_notMem (x : ProjectiveSpectrum 𝒜) :
    ∃ (f : A) (m : ℕ), f ∈ 𝒜 m ∧ 0 < m ∧ f ∉ x.asHomogeneousIdeal := by
  classical
  by_contra! h
  refine x.not_irrelevant_le fun z hz ↦ ?_
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  exact x.1.toIdeal.sum_mem fun k hk ↦ h _ k (SetLike.coe_mem _) <| by_contra <| by aesop
