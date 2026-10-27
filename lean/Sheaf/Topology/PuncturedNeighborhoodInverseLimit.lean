/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Topology.PuncturedNeighborhoodSpectralSystem
public import Sheaf.Topology.OpenSystemRestrictionPresentation

/-! # The punctured-neighborhood inverse limit

Source: Stacks Project, Cohomology, Tags 0A3D and 0A37.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace Opposite Topology
namespace TopCat

/-- The open at a stage of the punctured system.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
def puncturedStageOpen {T : Type u} [TopologicalSpace T] (Z : Set T) (hZ : IsClosed Z)
    (i : puncturedNeighborhoodIndex Z) : Opens T := puncturedNeighborhoodOpen Z hZ i

/-- Inclusions of punctured stages reverse the shrinking-neighborhood order.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
theorem puncturedStageOpen_antitone {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z) : Antitone (puncturedStageOpen Z hZ) :=
  fun _ _ h ↦ (puncturedNeighborhoodOpen Z hZ).monotone h

/-- The punctured generalization subspace lies in every stage.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
theorem puncturedStageOpen_contains {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z) (i : puncturedNeighborhoodIndex Z) :
    puncturedGeneralizations Z ⊆ puncturedStageOpen Z hZ i :=
  fun x hx ↦ @puncturedGeneralizations_le_preimage T _ Z hZ i ⟨x, hx⟩ True.intro


variable {T : Type u} [TopologicalSpace T] [SpectralSpace T]

instance (Z : Set T) : Nonempty (puncturedNeighborhoodIndex Z) :=
  puncturedNeighborhoodIndex_nonempty Z

instance (Z : Set T) : IsDirected (puncturedNeighborhoodIndex Z) (· ≤ ·) :=
  puncturedNeighborhoodIndex_directed Z

/-- Each punctured stage is compact when the complement of Z is compact.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
theorem puncturedStageOpen_compact (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (i : puncturedNeighborhoodIndex Z) : IsCompact (puncturedStageOpen Z hZ i : Set T) :=
  i.property.2.inter_of_isOpen hU i.val.isOpen hZ.isOpen_compl

/-- A punctured stage is a spectral compact open subspace.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
theorem puncturedStageOpen_spectral (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (i : puncturedNeighborhoodIndex Z) : SpectralSpace (puncturedStageOpen Z hZ i) :=
  puncturedNeighborhoodSpace_spectral Z hZ hU i

/-- A transition inclusion between punctured stages.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
abbrev puncturedStageMap (Z : Set T) (hZ : IsClosed Z)
    (i j : puncturedNeighborhoodIndex Z) (h : i ≤ j) :=
  OpenSystem.inclusionOfLE (puncturedStageOpen_antitone Z hZ h)

/-- The projection from the common punctured subspace.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
abbrev puncturedStageProjection (Z : Set T) (hZ : IsClosed Z)
    (i : puncturedNeighborhoodIndex Z) :=
  OpenSystem.inclusionOfLE (puncturedStageOpen_contains Z hZ i)

/-- Transitions have compact preimages of compact opens.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
theorem puncturedStageMap_spectral (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (i j : puncturedNeighborhoodIndex Z) (h : i ≤ j) :
    IsSpectralMap (puncturedStageMap Z hZ i j h) :=
  puncturedNeighborhoodTransition_spectral Z hZ hU i j h

/-- Compatible stage points are exactly one point of the punctured generalizations.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
theorem puncturedStageProjection_limit (Z : Set T) (hZ : IsClosed Z)
    (s : ∀ i : puncturedNeighborhoodIndex Z, puncturedStageOpen Z hZ i)
    (hs : ∀ (i j : puncturedNeighborhoodIndex Z) (h : i ≤ j),
      puncturedStageMap Z hZ i j h (s j) = s i) :
    ∃! x : puncturedGeneralizations Z, ∀ i, puncturedStageProjection Z hZ i x = s i :=
  (puncturedNeighborhood_topologicalLimit Z hZ).1 s hs

/-- The projections induce precisely the subspace topology.
Source: Stacks Project, Topology, Tags 0A31 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
theorem puncturedStageProjection_initial (Z : Set T) (hZ : IsClosed Z) :
    (inferInstance : TopologicalSpace (puncturedGeneralizations Z)) =
      ⨅ i : puncturedNeighborhoodIndex Z,
        TopologicalSpace.induced (puncturedStageProjection Z hZ i) inferInstance :=
  (puncturedNeighborhood_topologicalLimit Z hZ).2

/-- The punctured generalizations form a spectral inverse limit of compact opens.
Source: Stacks Project, Topology, Tags 0A31, 0902 and 0A2Z.
(blueprint: lem-weil-pbc-punctured-neighborhood-inverse-limit) -/
theorem puncturedNeighborhood_inverseLimit (Z : Set T) (hZ : IsClosed Z)
    (hU : IsCompact Zᶜ) : SpectralSpace (puncturedGeneralizations Z) :=
  puncturedGeneralizations_spectral Z hZ hU

end TopCat
