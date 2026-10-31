/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.PuncturedNeighborhoodCohomologyDiagram
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.Topology.PuncturedNeighborhoodCohomologyClassLift
import WeilConjectures.Topology.PuncturedNeighborhoodCohomologyEventualZero
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Cohomology of punctured generalization neighborhoods

Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: lem-weil-pbc-punctured-neighborhood-cohomology-colimit)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat

private theorem neighborhoodIndex_filtered
    {T : Type u} [TopologicalSpace T] [SpectralSpace T] (Z : Set T) :
    IsFiltered (compactOpenNeighborhoods Z)ᵒᵖ where
  nonempty := ⟨op ⟨⊤, Set.subset_univ _, isCompact_univ⟩⟩
  cocone_objs N M := by
    let K : compactOpenNeighborhoods Z :=
      ⟨(unop N).val ⊓ (unop M).val,
        (fun _ hz ↦ ⟨(unop N).property.1 hz, (unop M).property.1 hz⟩),
        (unop N).property.2.inter_of_isOpen (unop M).property.2
          (unop N).val.isOpen (unop M).val.isOpen⟩
    exact ⟨op K, (homOfLE (show K ≤ unop N from fun _ hx ↦ hx.1)).op,
      (homOfLE (show K ≤ unop M from fun _ hx ↦ hx.2)).op, True.intro⟩
  cocone_maps {X Y} f g := ⟨_, 𝟙 _, Subsingleton.elim _ _⟩


/-- Canonical restriction identifies cohomology of the punctured generalization subspace
with the filtered colimit over quasi-compact open neighborhoods of the closed subset.
Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: lem-weil-pbc-punctured-neighborhood-cohomology-colimit)

Proof:
1. The neighborhood index contains `T` and is directed by intersection. A point specializing
into `Z` lies in every neighborhood. Conversely, a point whose closure misses `Z` can be
excluded by a finite union of compact basis opens covering `Z`. Thus `W` is the intersection
of these neighborhoods, and `S = W \ Z` is the intersection of their punctures. This also
works for empty `Z`, using the empty union.
2. Each puncture `N \ Z` is compact open, using quasi-separatedness and compactness of the
open complement. A compact open subspace of a spectral space is spectral, by restricting
the compact-open basis and its intersection property, and restricting generic points of
irreducible closed subsets. Its transition inclusions are spectral for the same reason.
3. Compatible tuples in the punctured neighborhoods are a single point in their
intersection. The topology is the initial topology, since the coordinate `N = T` already
induces the subspace topology. Apply `lem-weil-pbc-spectral-directed-limit-spectral` to
obtain spectrality of `S` and its projections (Stacks, Topology, Tag 0A2Z).
4. Inverse image to opens is restriction. The inverse-image composition isomorphisms,
characterized by compatibility with adjunction units, identify every pulled-back coefficient
sheaf with `A|_S`. The transitions become identities by associativity of those isomorphisms.
The resulting constant diagram has colimit `A|_S`, since the index is nonempty and directed.
5. Apply `lem-weil-pbc-spectral-limit-cohomology` (Stacks, Cohomology, Tag 0A37) to the
spectral limit and coefficient system just constructed. Its comparison legs are pullback
followed by the coefficient coprojections, which under step 4 are precisely the canonical
restrictions used in `puncturedNeighborhoodCohomologyCocone`. Thus the canonical induced
map, rather than only an unspecified map between the groups, is an isomorphism. -/
theorem puncturedNeighborhoodCohomology_colimit
    {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (p : ℕ) :
    IsFiltered (compactOpenNeighborhoods Z)ᵒᵖ ∧
      IsIso (colimit.desc (puncturedNeighborhoodCohomologyDiagram Z hZ A p)
        (puncturedNeighborhoodCohomologyCocone Z hZ A p)) := by
  classical
  have := neighborhoodIndex_filtered Z
  refine ⟨inferInstance, ?_⟩
  let D := puncturedNeighborhoodCohomologyDiagram Z hZ A p
  let C := puncturedNeighborhoodCohomologyCocone Z hZ A p
  apply (ConcreteCategory.isIso_iff_bijective (colimit.desc D C)).2
  constructor
  · apply (injective_iff_map_eq_zero (colimit.desc D C).hom).2
    intro z hz
    obtain ⟨N, x, rfl⟩ := Concrete.colimit_exists_rep D z
    have hx : (C.ι.app N).hom x = 0 := by
      change (colimit.ι D N ≫ colimit.desc D C).hom x = 0 at hz
      rwa [colimit.ι_desc] at hz
    obtain ⟨M, f, hf⟩ := puncturedNeighborhood_cohomology_eventual_zero Z hZ hU A p N x hx
    calc
      (colimit.ι D N).hom x = (colimit.ι D M).hom ((D.map f).hom x) :=
        (colimit.w_apply D f x).symm
      _ = 0 := by rw [hf, map_zero]
  · intro y
    obtain ⟨N, x, hx⟩ := puncturedNeighborhood_cohomology_class_lift Z hZ hU A p y
    refine ⟨(colimit.ι D N).hom x, ?_⟩
    change (colimit.ι D N ≫ colimit.desc D C).hom x = y
    rw [colimit.ι_desc]
    exact hx

end TopCat
