/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Basic opens of `Proj`

We record `AlgebraicGeometry.Proj.basicOpen_add_le`, the analogue for `Proj.basicOpen`
of `AlgebraicGeometry.Scheme.basicOpen_add_le`: `D₊(f + g) ⊆ D₊(f) ∪ D₊(g)`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {σ : Type u} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The basic open of a sum is covered by the basic opens of the summands:
`D₊(f + g) ⊆ D₊(f) ∪ D₊(g)`. -/
lemma Proj.basicOpen_add_le (f g : A) :
    Proj.basicOpen 𝒜 (f + g) ≤ Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g := by
  intro x hx
  rw [Proj.mem_basicOpen] at hx
  rw [TopologicalSpace.Opens.mem_sup, Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_contra h
  rw [not_or, not_not, not_not] at h
  exact hx (add_mem h.1 h.2)

end AlgebraicGeometry
