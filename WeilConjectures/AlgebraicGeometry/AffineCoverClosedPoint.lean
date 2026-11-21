/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Finite affine covers isolating a closed point

A quasi-compact scheme with a closed point `x` has a finite affine open cover in which exactly
one member contains `x`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_finite_affine_cover_unique_mem`
-/

@[expose] public section

universe u

open TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact scheme `X` with a closed point `x` has a finite cover by affine opens, indexed
by a type in the universe of `X`, of which exactly one member contains `x`. -/
lemma exists_finite_affine_cover_unique_mem (X : Scheme.{u}) [CompactSpace X] {x : X}
    (hx : IsClosed {x}) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → X.Opens) (i₀ : ι), (∀ i, IsAffineOpen (U i)) ∧
      iSup U = ⊤ ∧ ∀ i, x ∈ U i ↔ i = i₀ := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let T := {V : X.affineOpens // x ∉ (V : X.Opens)}
  have hcov : (V₀ : Set X)ᶜ ⊆ ⋃ V : T, ((V.1 : X.Opens) : Set X) := by
    intro z hz
    have hzx : z ∈ ({x}ᶜ : Set X) := fun h ↦ hz (by rw [Set.mem_singleton_iff.1 h]; exact hxV₀)
    obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVx⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hzx hx.isOpen_compl
    exact Set.mem_iUnion.2 ⟨⟨⟨V, hV⟩, fun h ↦ hVx h rfl⟩, hzV⟩
  obtain ⟨t, ht⟩ := (V₀.isOpen.isClosed_compl.isCompact).elim_finite_subcover
    (fun V : T ↦ ((V.1 : X.Opens) : Set X)) (fun V ↦ (V.1 : X.Opens).isOpen) hcov
  refine ⟨Option t, inferInstance, fun i ↦ i.elim V₀ fun V ↦ (V.1.1 : X.Opens), none,
    fun i ↦ ?_, eq_top_iff.2 fun z _ ↦ ?_, fun i ↦ ?_⟩
  · cases i with
    | none => exact hV₀
    | some V => exact V.1.1.2
  · by_cases hz : z ∈ V₀
    · exact Opens.mem_iSup.2 ⟨none, hz⟩
    · obtain ⟨V, hV, hzV⟩ := Set.mem_iUnion₂.1 (ht hz)
      exact Opens.mem_iSup.2 ⟨some ⟨V, hV⟩, hzV⟩
  · cases i with
    | none => exact iff_of_true hxV₀ rfl
    | some V => exact iff_of_false V.1.2 (Option.some_ne_none _)

end AlgebraicGeometry.Scheme
