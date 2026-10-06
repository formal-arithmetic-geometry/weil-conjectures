/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace

/-!
# Dense constructible sets contain a dense open

In a Noetherian space, a constructible set dense in an irreducible closed set `t` contains a
nonempty open subset of `t`.

The other affine-geometric facts of the blueprint subsection are in Mathlib: the spectrum of a
finitely generated algebra over a field is Noetherian (`Algebra.FiniteType.isNoetherianRing` and
`PrimeSpectrum.instNoetherianSpace`), a Noetherian space has finitely many irreducible components
(`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`), and the image of a constructible
set under a morphism of finite presentation is constructible (Chevalley,
`PrimeSpectrum.isConstructible_comap_image`).

## Main results

- `Topology.IsConstructible.exists_isOpen_inter_subset_or`: over an irreducible set, a
  constructible set generically contains it or misses it.
- `exists_isOpen_inter_subset_of_isConstructible`

## Blueprint

- `sk-i-geometry`: dense constructible sets.
-/

@[expose] public section

open Topology

/-- Over an irreducible set `t`, a constructible set `s` is generically either everything or
nothing: some open set meeting `t` has its trace on `t` contained in `s` or in `sᶜ`. -/
theorem Topology.IsConstructible.exists_isOpen_inter_subset_or {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsConstructible s) (hirr : IsIrreducible t) :
    (∃ u : Set X, IsOpen u ∧ (u ∩ t).Nonempty ∧ u ∩ t ⊆ s) ∨
      ∃ u : Set X, IsOpen u ∧ (u ∩ t).Nonempty ∧ u ∩ t ⊆ sᶜ := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases hUt : (U ∩ t).Nonempty
    · exact .inl ⟨U, hU, hUt, Set.inter_subset_left⟩
    · refine .inr ⟨Set.univ, isOpen_univ, by simpa using hirr.nonempty, fun x hx hxU ↦ ?_⟩
      exact hUt ⟨x, hxU, hx.2⟩
  | union s _ s' _ h h' =>
    rcases h with ⟨u, hu, hut, hus⟩ | ⟨u, hu, hut, hus⟩
    · exact .inl ⟨u, hu, hut, hus.trans Set.subset_union_left⟩
    rcases h' with ⟨u', hu', hut', hus'⟩ | ⟨u', hu', hut', hus'⟩
    · exact .inl ⟨u', hu', hut', hus'.trans Set.subset_union_right⟩
    obtain ⟨x, hxt, hxu, hxu'⟩ := hirr.2 u u' hu hu' (by rwa [Set.inter_comm])
      (by rwa [Set.inter_comm])
    refine .inr ⟨u ∩ u', hu.inter hu', ⟨x, ⟨hxu, hxu'⟩, hxt⟩, ?_⟩
    rintro y ⟨⟨hyu, hyu'⟩, hyt⟩ (hy | hy)
    exacts [hus ⟨hyu, hyt⟩ hy, hus' ⟨hyu', hyt⟩ hy]
  | compl s _ h => simpa only [compl_compl, or_comm] using h

/-- In a Noetherian space, a constructible set `s` dense in an irreducible closed set `t` contains
a nonempty open subset of `t`. (blueprint: `sk-i-geometry`)

The Noetherian and closedness hypotheses are not needed for the proof. -/
theorem exists_isOpen_inter_subset_of_isConstructible {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {s t : Set X} (hs : IsConstructible s) (_ht : IsClosed t)
    (hirr : IsIrreducible t) (hst : closure s = t) :
    ∃ u : Set X, IsOpen u ∧ (u ∩ t).Nonempty ∧ u ∩ t ⊆ s := by
  refine (hs.exists_isOpen_inter_subset_or hirr).resolve_right ?_
  rintro ⟨u, hu, ⟨x, hxu, hxt⟩, hus⟩
  have hsu : s ⊆ uᶜ := fun y hys hyu ↦ hus ⟨hyu, hst ▸ subset_closure hys⟩ hys
  exact (closure_minimal hsu hu.isClosed_compl) (hst ▸ hxt) hxu
