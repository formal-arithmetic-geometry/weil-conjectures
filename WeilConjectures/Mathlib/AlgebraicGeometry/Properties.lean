/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Properties

/-!
# Quasi-compact opens of a scheme

Two consequences of a scheme having a basis of quasi-compact (indeed affine) opens:

- `AlgebraicGeometry.Scheme.exists_isCompact_opens_of_isCompact_of_isOpen`: every
  compact subset of an open subset is contained in a quasi-compact open subset of that
  open subset;
- `AlgebraicGeometry.Scheme.exists_disjoint_constructibleClosed_separation`: in a
  quasi-compact scheme, two disjoint closed subsets are separated by quasi-compact
  opens, hence by disjoint constructible closed supersets.

Nothing here uses the structure sheaf; the scheme structure enters only through
`AlgebraicGeometry.Scheme.isBasis_affineOpens`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Every compact subset of an open subset of a scheme is contained in a quasi-compact
open subset of that open subset: cover the compact set by finitely many affine opens
inside the open set. -/
theorem Scheme.exists_isCompact_opens_of_isCompact_of_isOpen (V : Scheme.{u})
    {C O : Set V} (hC : IsCompact C) (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ W : V.Opens, IsCompact (W : Set V) ∧ C ⊆ (W : Set V) ∧ (W : Set V) ⊆ O := by
  have H : ∀ x : C, ∃ W : V.affineOpens, (x : V) ∈ W.1 ∧ (W.1 : Set V) ⊆ O := by
    rintro ⟨x, hx⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ :=
      V.isBasis_affineOpens.exists_subset_of_mem_open (hCO hx) hO
    exact ⟨⟨W, hW⟩, hxW, hWO⟩
  choose Wx hxW hWO using H
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C ↦ ((Wx x).1 : Set V))
    (fun x ↦ (Wx x).1.isOpen)
    (fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  refine ⟨⨆ x ∈ t, (Wx x).1, ?_, ?_, ?_⟩
  · have hset : ((⨆ x ∈ t, (Wx x).1 : V.Opens) : Set V) =
        ⋃ x ∈ t, ((Wx x).1 : Set V) := by
      simp
    rw [hset]
    exact t.finite_toSet.isCompact_biUnion fun x _ ↦ (Wx x).2.isCompact
  · intro z hz
    obtain ⟨x, hxt, hzx⟩ := Set.mem_iUnion₂.mp (ht hz)
    have : z ∈ (⋃ x ∈ t, ((Wx x).1 : Set V)) := Set.mem_iUnion₂.mpr ⟨x, hxt, hzx⟩
    simpa using this
  · intro z hz
    have : z ∈ (⋃ x ∈ t, ((Wx x).1 : Set V)) := by simpa using hz
    obtain ⟨x, -, hzx⟩ := Set.mem_iUnion₂.mp this
    exact hWO x hzx

/-- **Separation of disjoint closed subsets by quasi-compact opens** in a
quasi-compact scheme: for disjoint closed `T`, `T'` there are quasi-compact opens
`W ⊇ T'` disjoint from `T` and `W' ⊇ Wᶜ` disjoint from `T'`. The complements `Wᶜ` and
`W'ᶜ` are then the disjoint constructible closed supersets of `T` and `T'` required
by the boundary preparation.
(Blueprint: `lemma:nagata-spectral-constructible-separation-exists`,
`lemma:nagata-spectral-constructible-separation`.) -/
theorem Scheme.exists_disjoint_constructibleClosed_separation (V : Scheme.{u})
    [CompactSpace V] {T T' : Set V} (hT : IsClosed T) (hT' : IsClosed T')
    (hdisj : Disjoint T T') :
    ∃ W W' : V.Opens, IsCompact (W : Set V) ∧ IsCompact (W' : Set V) ∧
      T' ⊆ (W : Set V) ∧ Disjoint (W : Set V) T ∧
      (W : Set V)ᶜ ⊆ (W' : Set V) ∧ Disjoint (W' : Set V) T' := by
  obtain ⟨W, hWc, hT'W, hWT⟩ := V.exists_isCompact_opens_of_isCompact_of_isOpen
    hT'.isCompact hT.isOpen_compl (hdisj.symm.subset_compl_right)
  obtain ⟨W', hW'c, hWcW', hW'T'⟩ := V.exists_isCompact_opens_of_isCompact_of_isOpen
    (W.isOpen.isClosed_compl.isCompact) hT'.isOpen_compl
    (Set.compl_subset_compl.mpr hT'W)
  exact ⟨W, W', hWc, hW'c, hT'W,
    Set.disjoint_of_subset_left hWT disjoint_compl_left,
    hWcW', Set.disjoint_of_subset_left hW'T' disjoint_compl_left⟩

end AlgebraicGeometry
