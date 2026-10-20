/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Topology.PuncturedNeighborhoodCohomologyColimit
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.NoetherianTopologicalCohomologyVanishing
import WeilConjectures.Topology.EmptySpaceCohomologyVanishing
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # Extending top-degree abelian cohomology classes

Source: Stacks Project, Cohomology, Tag 0A3G (2).
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite Order

open CategoryTheory.Functor.sheafPullbackConstruction

namespace TopCat

private theorem puncturedGeneralizations_stable {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z) {x y : T} (hx : x ∈ puncturedGeneralizations Z)
    (hy : y ⤳ x) : y ∈ puncturedGeneralizations Z := by
  obtain ⟨⟨z, hzx, hz⟩, hxZ⟩ := hx
  refine ⟨⟨z, ?_, hz⟩, ?_⟩
  · exact specializes_iff_mem_closure.mp (hy.trans (specializes_iff_mem_closure.mpr hzx))
  · intro hyZ
    exact hxZ ((closure_minimal (Set.singleton_subset_iff.mpr hyZ) hZ)
      (specializes_iff_mem_closure.mp hy))

private theorem puncturedGeneralizations_dimension {T : Type u} [TopologicalSpace T]
    [QuasiSober T] (Z : Set T) (hZ : IsClosed Z) (d : ℕ)
    (hdim : topologicalKrullDim T ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim (puncturedGeneralizations Z) ≤ (d : WithBot ℕ∞) := by
  let S := puncturedGeneralizations Z
  let f := IrreducibleCloseds.map (Subtype.val : S → T) continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing
    IsInducing.subtypeVal
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  let D := f l.head
  obtain ⟨y, hy⟩ := QuasiSober.sober D.isIrreducible D.isClosed
  obtain ⟨x, hx⟩ := l.head.isIrreducible.nonempty
  have hxD : (x : T) ∈ (D : Set T) :=
    subset_closure (Set.mem_image_of_mem Subtype.val hx)
  have hyS : y ∈ S := puncturedGeneralizations_stable Z hZ x.property
    (hy.specializes hxD)
  obtain ⟨z, hzy, hz⟩ := hyS.1
  let E : IrreducibleCloseds T :=
    ⟨closure ({z} : Set T), isIrreducible_singleton.closure, isClosed_closure⟩
  have hED : E < D := by
    refine lt_of_le_of_ne (show (E : Set T) ⊆ D from
      closure_minimal (Set.singleton_subset_iff.mpr ?_) D.isClosed) ?_
    · exact hy ▸ hzy
    · intro heq
      have hyE : y ∈ (E : Set T) := heq ▸ hy.mem
      exact hyS.2 (closure_minimal (Set.singleton_subset_iff.mpr hz) hZ hyE)
  have hhead : E < (l.map f hf).head := by simpa using hED
  have hlen := (LTSeries.length_le_krullDim ((l.map f hf).cons E hhead)).trans hdim
  simp only [RelSeries.cons_length, LTSeries.map_length] at hlen
  have hn : l.length + 1 ≤ d + 1 := by exact_mod_cast hlen
  exact_mod_cast (Nat.le_of_succ_le_succ hn)

private theorem puncturedGeneralizations_cohomology_zero
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] [QuasiSober T] [T0Space T]
    (Z : Set T) (hZ : IsClosed Z) (d : ℕ)
    (hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
    IsZero (CategoryTheory.Sheaf.H'
      ((sheafPullback (Opens.map (puncturedGeneralizationsInclusion Z)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology T)
        (Opens.grothendieckTopology (puncturedGeneralizations Z))).obj A) d ⊤) := by
  cases d with
  | zero =>
    have h := IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero
      (X := T) (Z := Set.univ) isClosed_univ (by
        rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ T).isHomeomorph]
        exact hdim)
    have : T1Space T := ⟨fun x ↦ by simpa using h.2 x (Set.mem_univ x)⟩
    have : IsEmpty (puncturedGeneralizations Z) := ⟨by
      rintro ⟨x, ⟨⟨z, hz, hzZ⟩, hxZ⟩⟩
      simp only [closure_singleton, Set.mem_singleton_iff] at hz
      exact hxZ (hz ▸ hzZ)⟩
    exact cohomology_vanishing_of_isEmpty _ _ _
  | succ d =>
    exact isZero_noetherian_topological_cohomology_of_dimension_bound
      (puncturedGeneralizations Z) d
      (puncturedGeneralizations_dimension Z hZ d hdim) _ (d + 1) (by omega)

/-- A top-degree class on an open becomes zero on its intersection with some open
neighborhood of the closed complement.
Source: Stacks Project, Tag 0A3G (2), punctured-neighborhood paragraph, using
Tags 0A3D and 02UZ. (blueprint: lem-weil-pbc-top-degree-abelian-neighborhood-zero).

Proof: The punctured generalization subspace has dimension at most d-1 for d>0:
close a chain of irreducible closed subsets in the ambient space and prepend the
closure of a specialization in the complement. In degree zero the ambient space
has closed singletons and the punctured subspace is empty. Noetherian vanishing
(or the empty-space case) kills degree d on that subspace. The punctured-neighborhood
comparison identifies this zero group with the filtered colimit. Equality with zero
in a filtered colimit is witnessed after a transition to one smaller neighborhood.
The transition is precisely restriction to that neighborhood intersected with U. -/
theorem top_degree_abelian_neighborhood_zero
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] [SpectralSpace T]
    (d : ℕ) (hdim : topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (U : Opens T) (x : A.H' d U) :
    ∃ N : Opens T, (U : Set T)ᶜ ⊆ N ∧
      (A.cohomologyPresheaf d).map (homOfLE (inf_le_right : N ⊓ U ≤ U)).op x = 0 := by
  sorry



end TopCat
