/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GenericFiber.SpreadingOut
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.LimitBaseChange
public import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothLimit
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Spreading out a smooth dense open from the generic fibre

Let `B` be a Noetherian domain with fraction field `L`, `σ : Spec B ⟶ S` and `f : X ⟶ S` of
finite type. Suppose the generic fibre `X_L = X ×_S Spec L` has a dense open `W` with a
surjective closed immersion `Z ⟶ W` from a scheme `Z` smooth over `L`. Then for some nonzero
`r ∈ B`, the base change `X_r = X ×_S Spec B[1/r]` has an open immersed smooth `B[1/r]`-scheme
`V`, and over a nonempty open `O ⊆ Spec B[1/r]` every point of `X_r` is a specialization of a
point of `V` (`AlgebraicGeometry.exists_isImmersion_smooth_of_isFractionRing`).

`Spec L` is the limit of the `Spec B[1/r]`; the data descend to some stage by
`AlgebraicGeometry.exists_open_isClosedImmersion_of_isLimit_pt` and
`AlgebraicGeometry.Scheme.exists_smooth_pullback_snd_of_isLimit`, and `O` is the complement of
the closures of the images of the generic points of `X_r` outside `V`, none of which lies over
the generic point of `Spec B[1/r]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- In a quasi-sober space every point is a specialization of the generic point of an
irreducible component. -/
lemma exists_mem_irreducibleComponents_specializes {X : Type*} [TopologicalSpace X] [QuasiSober X]
    (x : X) : ∃ y : X, closure {y} ∈ irreducibleComponents X ∧ y ⤳ x := by
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := x)).closure
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hirr : IsIrreducible C := hC.1
  have hg : closure {hirr.genericPoint} = C := by
    rw [IsIrreducible.genericPoint_closure_eq hirr, hCc.closure_eq]
  refine ⟨hirr.genericPoint, hg.symm ▸ hC, ?_⟩
  rw [specializes_iff_mem_closure, hg]
  exact hxC (subset_closure rfl)

/-- In a space with finitely many irreducible components, a dense open contains the generic
point of every irreducible component. -/
lemma mem_of_dense_of_closure_mem_irreducibleComponents {X : Type*} [TopologicalSpace X]
    (hX : (irreducibleComponents X).Finite) {U : Set X} (hU : Dense U) (hUo : IsOpen U) {y : X}
    (hy : closure {y} ∈ irreducibleComponents X) : y ∈ U := by
  have h := closure_sUnion_irreducibleComponents_sdiff_singleton hX _ hy
  have hO : IsOpen (⋃₀ (irreducibleComponents X \ {closure {y}}))ᶜ := by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hX.sdiff.isClosed_biUnion fun C hC ↦ isClosed_of_mem_irreducibleComponents C hC.1
  have hne : (⋃₀ (irreducibleComponents X \ {closure {y}}))ᶜ.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at h
    exact (Set.singleton_nonempty y).ne_empty (Set.subset_empty_iff.mp (h ▸ subset_closure))
  obtain ⟨w, hwO, hwU⟩ := hU.inter_open_nonempty _ hO hne
  have hyw : y ⤳ w := by
    rw [specializes_iff_mem_closure, ← h]
    exact subset_closure hwO
  exact hyw.mem_open hUo hwU
