/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.PuncturedNeighborhoodCohomologyDiagram
public import Mathlib.Topology.Spectral.Basic
import WeilConjectures.Topology.PuncturedNeighborhoodInverseLimit
import WeilConjectures.Topology.OpenSystemColimitCohomologyComparison
import WeilConjectures.Topology.PuncturedNeighborhoodSpectralClassStageLift
import WeilConjectures.Topology.PuncturedNeighborhoodLegOpenSubspaceComparison

/-! # Elementwise punctured-neighborhood cohomology continuity -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace TopCat


private theorem transport_class {B C D : AddCommGrpCat.{u}} (e : C ≅ D)
    (f : B ⟶ C) (g : B ⟶ D) (hf : f ≫ e.hom = g)
    (x : B) (y : D) (hx : f.hom x = e.inv.hom y) : g.hom x = y := by
  have he : e.hom.hom (e.inv.hom y) = y :=
    congrArg (fun m ↦ m.hom y) e.inv_hom_id
  exact (congrArg (fun m ↦ m.hom x) hf).symm.trans
    ((congrArg e.hom.hom hx).trans he)

private theorem iso_preimage_apply {B C D : AddCommGrpCat.{u}} (e : B ≅ C)
    (f : C ⟶ D) (x : C) (y : D) (h : f.hom x = y) :
    (e.hom ≫ f).hom (e.inv.hom x) = y := by
  have he : e.hom.hom (e.inv.hom x) = x :=
    congrArg (fun m ↦ m.hom x) e.inv_hom_id
  exact (congrArg f.hom he).trans h

/-- Every cohomology class on the punctured generalization subspace extends to a
punctured compact open neighborhood.
Source: Stacks Project, Cohomology, Tags 0A3D(2) and 0A37.
(blueprint: lem-weil-pbc-punctured-neighborhood-cohomology-class-lift)

Proof: Reverse inclusion makes the compact open neighborhoods a nonempty directed set.
Their punctures are compact open spectral spaces, since the complement of Z is compact.
They intersect in the punctured generalizations: a point not specializing into Z is excluded
by a compact open neighborhood of Z inside the complement of its closure. Compatible tuples
are points of this intersection and its subspace topology is initial, using the top stage.
The spectral inverse-limit theorem applies. Restrict A to each stage and use the adjunction
units for the transition maps. The inverse-image composition isomorphisms identify all
pullbacks on the limit with A restricted there, hence their directed colimit is that sheaf.
The class-lifting half of cohomological continuity (0A37) now lifts the given class. Identify
open-subspace cohomology with ambient object cohomology by restriction of injective
resolutions, which preserves injectives since extension by zero is exact. Naturality and
unit normalization identify the comparison with the specified canonical cocone leg. -/
theorem puncturedNeighborhood_cohomology_class_lift
    {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z) (hU : IsCompact Zᶜ)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (q : ℕ)
    (y : (puncturedNeighborhoodCohomologyCocone Z hZ A q).pt) :
    ∃ (N : (compactOpenNeighborhoods Z)ᵒᵖ)
      (x : (puncturedNeighborhoodCohomologyDiagram Z hZ A q).obj N),
      ((puncturedNeighborhoodCohomologyCocone Z hZ A q).ι.app N).hom x = y := by
  classical
  let I := puncturedNeighborhoodIndex Z
  let V : I → Opens T := puncturedStageOpen Z hZ
  let E := puncturedGeneralizations Z
  let hE : ∀ i : I, E ⊆ V i := puncturedStageOpen_contains Z hZ
  let eH := OpenSystem.coefficientCohomologyColimitIso (I := I) E A q
  obtain ⟨i, x, hx⟩ := punctured_spectral_class_stage_lift Z hZ hU A q (eH.inv.hom y)
  obtain ⟨eV, _heVcanonical, hleg⟩ :=
    puncturedNeighborhoodLeg_openSubspace_comparison Z hZ A q i (hE i)
  refine ⟨op i, eV.inv.hom x, ?_⟩
  have htransport := OpenSystem.coefficientColimit_cohomology_comparison V E hE A q i
  have hstage := transport_class eH _ _ htransport x y hx
  change (puncturedNeighborhoodCohomologyLeg Z hZ A q i).hom (eV.inv.hom x) = y
  exact (congrArg (fun m ↦ m.hom (eV.inv.hom x)) hleg).trans
    (iso_preimage_apply eV _ x y hstage)

end TopCat
