/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Topology.CanonicalCohomologyPullback

/-! # The punctured-neighborhood cohomology diagram and its canonical cocone

Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace TopCat

/-- Points outside `Z` which specialize to some point of `Z`.
Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram) -/
def puncturedGeneralizations {T : Type u} [TopologicalSpace T] (Z : Set T) : Set T :=
  {t | (closure ({t} : Set T) ∩ Z).Nonempty ∧ t ∉ Z}

/-- Quasi-compact open neighborhoods, with their ordinary inclusion order.
The cohomology diagram uses the opposite category, hence reverse inclusion.
Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram) -/
abbrev compactOpenNeighborhoods {T : Type u} [TopologicalSpace T] (Z : Set T) :=
  {N : Opens T // Z ⊆ N ∧ IsCompact (N : Set T)}

/-- Inclusion of the punctured generalization subspace into the ambient space.
Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram) -/
def puncturedGeneralizationsInclusion {T : Type u} [TopologicalSpace T] (Z : Set T) :
    TopCat.of (puncturedGeneralizations Z) ⟶ TopCat.of T :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The monotone assignment `N ↦ N \ Z`.
Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram) -/
def puncturedNeighborhoodOpen {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z) : compactOpenNeighborhoods Z →o Opens T where
  toFun N := N.val ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  monotone' := fun _ _ h _ hx ↦ ⟨h hx.1, hx.2⟩

/-- The restriction diagram of cohomology groups of the punctured neighborhoods.
`H' A p V` is object cohomology on the open `V`, hence cohomology of `A|_V`.
Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram) -/
def puncturedNeighborhoodCohomologyDiagram {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (p : ℕ) :
    (compactOpenNeighborhoods Z)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (puncturedNeighborhoodOpen Z hZ).toFunctor.op ⋙ A.cohomologyPresheaf p

/-- Every punctured generalization is in every punctured open neighborhood.
Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram)

Proof: If `t` specializes to `z ∈ Z ⊆ N`, openness of `N` implies `t ∈ N`.
The definition of the punctured generalizations additionally gives `t ∉ Z`.
Thus the inverse image of `N \ Z` on this subspace is the whole space. -/
theorem puncturedGeneralizations_le_preimage {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z) (N : compactOpenNeighborhoods Z) :
    (⊤ : Opens (puncturedGeneralizations Z)) ≤
      (Opens.map (puncturedGeneralizationsInclusion Z)).obj
        (puncturedNeighborhoodOpen Z hZ N) := by
  sorry

/-- Canonical restriction from a punctured neighborhood to the generalization subspace.
Source: Stacks Project, Cohomology, Tags 0A3D (2), 01F8 and 01FB.
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram) -/
def puncturedNeighborhoodCohomologyLeg {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (p : ℕ)
    (N : compactOpenNeighborhoods Z) :
    (puncturedNeighborhoodCohomologyDiagram Z hZ A p).obj (op N) ⟶
      CategoryTheory.Sheaf.H'
        ((sheafPullback (Opens.map (puncturedGeneralizationsInclusion Z)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology T)
          (Opens.grothendieckTopology (puncturedGeneralizations Z))).obj A) p ⊤ :=
  objectCohomologyPullback (puncturedGeneralizationsInclusion Z) p
      (puncturedNeighborhoodOpen Z hZ N) A ≫
    (((sheafPullback (Opens.map (puncturedGeneralizationsInclusion Z)) AddCommGrpCat.{u}
      (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology (puncturedGeneralizations Z))).obj A).cohomologyPresheaf p).map
        (homOfLE (puncturedGeneralizations_le_preimage Z hZ N)).op

/-- Canonical restrictions are compatible with restriction between punctured neighborhoods.
Source: Stacks Project, Cohomology, Tags 0A3D (2), 01F8 and 01FB.
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram)

Proof: Object-cohomology restriction is natural in the open object. In degree zero this
is the sectionwise naturality of the inverse-image adjunction unit; in higher degrees
it follows by universality of the derived evaluation delta-functor. Composing with the
restriction from the inverse-image open to the whole subspace gives the same map for
two nested neighborhoods, by functoriality of `cohomologyPresheaf`. -/
theorem puncturedNeighborhoodCohomologyLeg_naturality
    {T : Type u} [TopologicalSpace T] (Z : Set T) (hZ : IsClosed Z)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (p : ℕ)
    {N M : (compactOpenNeighborhoods Z)ᵒᵖ} (f : N ⟶ M) :
    (puncturedNeighborhoodCohomologyDiagram Z hZ A p).map f ≫
      puncturedNeighborhoodCohomologyLeg Z hZ A p (unop M) =
        puncturedNeighborhoodCohomologyLeg Z hZ A p (unop N) := by
  sorry

/-- The canonical restriction cocone, with vertex `H^p(S,A|_S)`.
Source: Stacks Project, Cohomology, Tag 0A3D (2).
(blueprint: def-weil-pbc-punctured-neighborhood-cohomology-diagram) -/
def puncturedNeighborhoodCohomologyCocone {T : Type u} [TopologicalSpace T]
    (Z : Set T) (hZ : IsClosed Z)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (p : ℕ) :
    Cocone (puncturedNeighborhoodCohomologyDiagram Z hZ A p) where
  pt := CategoryTheory.Sheaf.H'
    ((sheafPullback (Opens.map (puncturedGeneralizationsInclusion Z)) AddCommGrpCat.{u}
      (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology (puncturedGeneralizations Z))).obj A) p ⊤
  ι :=
    { app := fun N ↦ puncturedNeighborhoodCohomologyLeg Z hZ A p (unop N)
      naturality := fun _ _ f ↦ (puncturedNeighborhoodCohomologyLeg_naturality Z hZ A p f).trans
        (Category.comp_id _).symm }

end TopCat
