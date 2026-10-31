/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Topology.PuncturedNeighborhoodCohomologyDiagram
public import WeilConjectures.Topology.OpenSystemRestrictionPresentation
public import WeilConjectures.Topology.SpectralLimitCohomologyMap
/-! # Comparison of the specified punctured-neighborhood leg
Source: Stacks Project, Cohomology, Tags 0A3D(2) and 01F8.
(blueprint: lem-weil-pbc-punctured-leg-open-subspace-comparison)
-/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace TopCat
/-- The specified cocone leg is the open-subspace comparison map.
Source: Stacks Project, Cohomology, Tags 0A3D(2) and 01F8.
(blueprint: lem-weil-pbc-punctured-leg-open-subspace-comparison)

Proof: Restrict an injective resolution to the open punctured neighborhood. Restriction
preserves injectives, since exact extension by zero is its left adjoint. Evaluating global
sections of that restricted resolution equals evaluation on the ambient open, giving
the canonical displayed comparison isomorphism. Its forward map specifies it uniquely.
The unit equation for inverse-image composition identifies the two degree-zero maps;
naturality and compatibility with connecting morphisms extend this equality to every
degree, by induction through an injective embedding.
Unfold puncturedNeighborhoodCohomologyLeg once. Its ambient inclusion and
OpenSystem.inclusion of puncturedGeneralizations are the same subtype-val morphism.
Rewrite this equality at the topological morphism before forming the cohomology family.
The terminal-open restriction arrows are equal by proof irrelevance in the thin category
of opens. This identifies the leg with the displayed right side.
No compactness, spectrality, or assertion about lifting classes enters this identification. -/
theorem puncturedNeighborhoodLeg_openSubspace_comparison
    {T : Type u} [TopologicalSpace T] (Z : Set T) (hZ : IsClosed Z)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (q : ℕ) (N : compactOpenNeighborhoods Z)
    (h : puncturedGeneralizations Z ⊆ puncturedNeighborhoodOpen Z hZ N) :
    ∃ e : CategoryTheory.Sheaf.H' A q (puncturedNeighborhoodOpen Z hZ N) ≅
        CategoryTheory.Sheaf.H' ((OpenSystem.inverseImage
          (OpenSystem.inclusion (puncturedNeighborhoodOpen Z hZ N : Set T))).obj A) q ⊤,
      e.hom = objectCohomologyPullback
          (OpenSystem.inclusion (puncturedNeighborhoodOpen Z hZ N : Set T)) q
          (puncturedNeighborhoodOpen Z hZ N) A ≫
        (((OpenSystem.inverseImage
          (OpenSystem.inclusion (puncturedNeighborhoodOpen Z hZ N : Set T))).obj
            A).cohomologyPresheaf q).map
          (homOfLE (show (⊤ : Opens (puncturedNeighborhoodOpen Z hZ N)) ≤
            (Opens.map (OpenSystem.inclusion
              (puncturedNeighborhoodOpen Z hZ N : Set T))).obj
                (puncturedNeighborhoodOpen Z hZ N) from fun x _ ↦ x.property)).op ∧
      puncturedNeighborhoodCohomologyLeg Z hZ A q N = e.hom ≫
        TopCat.Sheaf.spectralLimitCohomologyMap (OpenSystem.inclusionOfLE h)
          (objectCohomologyPullback (OpenSystem.inclusionOfLE h))
          ((OpenSystem.adjunction (OpenSystem.inclusionOfLE h)).homEquiv _ _
            (OpenSystem.restrictionIso h A).hom) q := by sorry
end TopCat
