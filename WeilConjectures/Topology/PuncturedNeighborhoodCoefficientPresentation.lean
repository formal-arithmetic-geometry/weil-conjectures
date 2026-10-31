/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Topology.PuncturedNeighborhoodSpectralSystem
public import WeilConjectures.Topology.SpectralLimitCohomologyMap
public import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Coefficients and cohomology maps for punctured neighborhoods

Source: Stacks Project, Cohomology, Tags 0A37 and 0A3D (2), restriction-system setup;
Sheaves, Section 008C; Cohomology, Tags 01F8 and 01FB.
(blueprint: lem-weil-pbc-punctured-neighborhood-coefficient-presentation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat

section
variable {T : Type u} [TopologicalSpace T] [SpectralSpace T]
variable (Z : Set T) (hZ : IsClosed Z)
variable (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (q : ℕ)
local notation "I" => puncturedNeighborhoodIndex Z
local notation "S" => puncturedNeighborhoodSpace Z hZ
local notation "f" => puncturedNeighborhoodTransition Z hZ
local notation "X" => TopCat.of (puncturedGeneralizations Z)
local notation "p" => puncturedNeighborhoodProjection Z hZ

/-- Continuity for the projection on open-set sites.
Source: Stacks Project, Sheaves, Tag 008C.
(blueprint: lem-weil-pbc-punctured-neighborhood-coefficient-presentation) -/
local instance projectionContinuous (i : I) : (Opens.map (p i)).IsContinuous
    (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map (p i)) (coverPreserving_opens_map (p i))

set_option backward.isDefEq.respectTransparency false in
/-- Restriction coefficients and their comparison maps, bundled to keep dependent
existential elimination from repeatedly expanding cohomology definitions.
Source: Stacks Project, Cohomology, Tags 0A37 and 0A3D (2).
(blueprint: lem-weil-pbc-punctured-neighborhood-coefficient-presentation) -/
structure PuncturedNeighborhoodCoefficients where
  F : ∀ i : I, (S i).Sheaf AddCommGrpCat.{u}
  α : ∀ (i j : I) (h : i ≤ j),
        F i ⟶ (Sheaf.pushforward AddCommGrpCat.{u} (f i j h)).obj (F j)
  P : I ⥤ (TopCat.of (puncturedGeneralizations Z)).Sheaf AddCommGrpCat.{u}
  hasColimit : HasColimit P
  eP : ∀ i : I, P.obj i ≅
        (sheafPullback (Opens.map (p i)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).obj (F i)
  eH : ∀ i : I, (puncturedNeighborhoodCohomologyDiagram Z hZ A q).obj (op (OrderDual.ofDual i)) ≅
        CategoryTheory.Sheaf.H' (F i) q ⊤
  eL : letI := hasColimit
    (puncturedNeighborhoodCohomologyCocone Z hZ A q).pt ≅
      CategoryTheory.Sheaf.H' (colimit P) q ⊤
  alpha_id : ∀ (i : I) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
        HEq ((α i i le_rfl).hom.app (op U) s) s
  alpha_comp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
        (U : Opens (S i)) (s : (F i).obj.obj (op U)),
        HEq ((α i k (hij.trans hjk)).hom.app (op U) s)
          ((α j k hjk).hom.app (op ((Opens.map (f i j hij)).obj U))
            ((α i j hij).hom.app (op U) s))
  pullback_compat : ∀ (i j : I) (h : i ≤ j) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
        HEq (((eP i).inv ≫ P.map (homOfLE h) ≫ (eP j).hom).hom.app
            (op ((Opens.map (p i)).obj U))
          (((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).unit.app
              (F i)).hom.app (op U) s))
          (((sheafAdjunctionContinuous (Opens.map (p j)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
              (F j)).hom.app (op ((Opens.map (f i j h)).obj U))
                ((α i j h).hom.app (op U) s))
  map_compat : ∀ (i j : I) (h : i ≤ j),
        (puncturedNeighborhoodCohomologyDiagram Z hZ A q).map
          (homOfLE (show OrderDual.ofDual j ≤ OrderDual.ofDual i from h)).op ≫
            (eH j).hom =
          (eH i).hom ≫ Sheaf.spectralLimitCohomologyMap (f i j h)
            (objectCohomologyPullback (f i j h)) (α i j h) q
  leg_compat : letI := hasColimit
    ∀ i : I, (puncturedNeighborhoodCohomologyCocone Z hZ A q).ι.app
      (op (OrderDual.ofDual i)) ≫ eL.hom =
        (eH i).hom ≫ Sheaf.spectralLimitCohomologyMap (p i)
          (objectCohomologyPullback (p i))
          ((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv
              (F i) (colimit P) ((eP i).inv ≫ colimit.ι P i)) q

end

set_option backward.isDefEq.respectTransparency false in
/-- The ambient cohomology diagram and cocone are the cohomology maps of the
restriction coefficient system. This asserts only identifications of sheaves and maps;
it asserts neither generation of cohomology classes nor detection of zero relations.
No compactness of the complement of Z is required.

Source: Stacks Project, Cohomology, Tags 0A37 and 0A3D (2), restriction-system setup;
Sheaves, Section 008C; Cohomology, Tags 01F8 and 01FB.
(blueprint: lem-weil-pbc-punctured-neighborhood-coefficient-presentation)

Proof: Write j_i : N_i minus Z → T and k : S → T for the inclusions. Take F_i to
be j_i inverse image of A. Direct images compose sectionwise; the adjunctions
therefore give inverse-image composition isomorphisms c(j_i,f_ij), uniquely
characterized by compatibility with the units. Let alpha_ij be the adjoint of
c(j_i,f_ij). The identity and associativity laws for these composition isomorphisms
follow by applying adjunction and comparing units, and give the two displayed
sectionwise laws for alpha. Take P to be constant with value k inverse image of A.
The inverses of c(j_i,p_i) are its comparison isomorphisms eP. Associativity and
unit compatibility give the displayed sectionwise law for P. The index contains
the ambient space and is directed by intersection, so it is connected and nonempty;
the constant cocone on P is a colimit. Identify colimit P with k inverse image of A.
For an open inclusion j, inverse image is ordinary sheaf restriction. Restrict an
injective resolution along j: extension by zero is exact and left adjoint to
restriction, so restriction preserves injectives. Sections on the whole subspace
are sections on the ambient open. Comparing these complexes, and the Ext and
derived-sections descriptions, gives the isomorphisms eH. Use the preceding colimit
identification for eL. In degree zero both displayed map identities are the unit
and restriction identities on sections. The comparisons are natural and commute
with connecting morphisms; uniqueness of normalized cohomology pullback gives
these identities in every degree. This also identifies the projection map with
the specified cocone leg, including its final restriction to the terminal open.
The same construction works for empty punctures and empty S, whose section and
cohomology groups are zero. -/
theorem puncturedNeighborhood_coefficient_presentation
    {T : Type u} [TopologicalSpace T] [SpectralSpace T]
    (Z : Set T) (hZ : IsClosed Z)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (q : ℕ) :
    Nonempty (PuncturedNeighborhoodCoefficients Z hZ A q) := by sorry

end TopCat
