/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Spectral.Prespectral

/-!
# Separation by compact opens in compact prespectral spaces

In a compact prespectral space — for instance the underlying space of a quasi-compact
scheme — two disjoint closed subsets can be covered away from each other by two
quasi-compact opens: there are compact opens `O₁`, `O₂` covering the space with
`O₁ ∩ T₁ = ∅` and `O₂ ∩ T₂ = ∅`.

Passing to complements, this says that disjoint closed subsets of a compact
prespectral space are contained in disjoint *constructible* closed subsets
(closed subsets with quasi-compact complement). This is the constructible
approximation step in the proof of Stacks Project Tag 0F3W: the boundary-separation
blow-up (Tag 0F3V, `AlgebraicGeometry.exists_admissibleBlowup_disjoint_closures`)
requires closed subsets with quasi-compact complements, and this lemma produces them
from plain disjoint closed subsets.
-/

@[expose] public section

open Set

variable {X : Type*} [TopologicalSpace X]

/-- **Separation by compact opens**: in a compact prespectral space, for two disjoint
closed subsets `T₁`, `T₂` there are compact opens `O₁`, `O₂` covering the space such
that `O₁` avoids `T₁` and `O₂` avoids `T₂`. Equivalently, the closed sets `O₁ᶜ ⊇ T₁`
and `O₂ᶜ ⊇ T₂` are disjoint and have quasi-compact complements.
(Constructible approximation step in the proof of Stacks Project Tag 0F3W.) -/
theorem PrespectralSpace.exists_isCompact_isOpen_disjoint_union_eq_univ
    [CompactSpace X] [PrespectralSpace X] {T₁ T₂ : Set X}
    (h₁ : IsClosed T₁) (h₂ : IsClosed T₂) (hd : Disjoint T₁ T₂) :
    ∃ O₁ O₂ : Set X, IsOpen O₁ ∧ IsOpen O₂ ∧ IsCompact O₁ ∧ IsCompact O₂ ∧
      Disjoint O₁ T₁ ∧ Disjoint O₂ T₂ ∧ O₁ ∪ O₂ = univ := by
  classical
  -- Around every point choose a compact open contained in `T₁ᶜ` or in `T₂ᶜ`.
  have key : ∀ x : X, ∃ V : Set X, IsOpen V ∧ IsCompact V ∧ x ∈ V ∧
      (V ⊆ T₁ᶜ ∨ V ⊆ T₂ᶜ) := by
    intro x
    have hx : x ∈ T₁ᶜ ∪ T₂ᶜ := by
      rw [← compl_inter, disjoint_iff_inter_eq_empty.mp hd, compl_empty]
      trivial
    obtain hx₁ | hx₂ := hx
    · obtain ⟨V, ⟨hVo, hVc⟩, hxV, hV⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx₁ h₁.isOpen_compl
      exact ⟨V, hVo, hVc, hxV, Or.inl hV⟩
    · obtain ⟨V, ⟨hVo, hVc⟩, hxV, hV⟩ :=
        PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx₂ h₂.isOpen_compl
      exact ⟨V, hVo, hVc, hxV, Or.inr hV⟩
  choose V hVo hVc hxV hV using key
  -- Extract a finite subcover of the resulting cover of the compact space `X`.
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ V hVo
    fun x _ ↦ mem_iUnion.mpr ⟨x, hxV x⟩
  -- Group the finitely many chosen compact opens by which closed set they avoid.
  refine ⟨⋃ x ∈ s.filter (fun x ↦ V x ⊆ T₁ᶜ), V x,
    ⋃ x ∈ s.filter (fun x ↦ ¬ V x ⊆ T₁ᶜ), V x,
    isOpen_biUnion fun x _ ↦ hVo x, isOpen_biUnion fun x _ ↦ hVo x,
    s.filter _ |>.isCompact_biUnion fun x _ ↦ hVc x,
    s.filter _ |>.isCompact_biUnion fun x _ ↦ hVc x, ?_, ?_, ?_⟩
  · exact disjoint_left.mpr fun a ha haT ↦ by
      obtain ⟨x, hx, hax⟩ := mem_iUnion₂.mp ha
      exact (Finset.mem_filter.mp hx).2 hax haT
  · refine disjoint_left.mpr fun a ha haT ↦ ?_
    obtain ⟨x, hx, hax⟩ := mem_iUnion₂.mp ha
    obtain hV₁ | hV₂ := hV x
    · exact (Finset.mem_filter.mp hx).2 hV₁
    · exact hV₂ hax haT
  · refine eq_univ_of_univ_subset fun a ha ↦ ?_
    obtain ⟨x, hx, hax⟩ := mem_iUnion₂.mp (hs ha)
    rw [mem_union, mem_iUnion₂, mem_iUnion₂]
    by_cases hcase : V x ⊆ T₁ᶜ
    · exact Or.inl ⟨x, Finset.mem_filter.mpr ⟨hx, hcase⟩, hax⟩
    · exact Or.inr ⟨x, Finset.mem_filter.mpr ⟨hx, hcase⟩, hax⟩
