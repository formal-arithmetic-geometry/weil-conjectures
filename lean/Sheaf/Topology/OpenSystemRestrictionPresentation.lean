/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Topology.CanonicalCohomologyPullback

/-! # Coefficients for a system of open subspaces

All coefficient objects and arrows below are actual inverse images and adjunction units.
No compactness, spectrality, or inverse-limit assertion is part of this presentation.

Source: Stacks Project, Cohomology, Tags 0A3D and 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation)
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace TopCat
namespace OpenSystem

variable {T : Type u} [TopologicalSpace T]

/-- Inclusion of a subspace.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
abbrev inclusion (E : Set T) : TopCat.of E ⟶ TopCat.of T :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- Inclusion of nested subspaces.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
def inclusionOfLE {E V : Set T} (h : E ⊆ V) : TopCat.of E ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val, h x.property⟩, continuous_subtype_val.subtype_mk _⟩

/-- The constructed inverse image, with its specified adjunction.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
abbrev inverseImage {X Y : TopCat.{u}} (f : X ⟶ Y) :=
  sheafPullback (Opens.map f) AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The adjunction of the constructed inverse image.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
abbrev adjunction {X Y : TopCat.{u}} (f : X ⟶ Y) :=
  sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

/-- The inverse-image composition isomorphism uniquely preserving the composite unit.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
@[irreducible] def restrictionIso {E V : Set T} (h : E ⊆ V)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
    (inverseImage (inclusionOfLE h)).obj ((inverseImage (inclusion V)).obj A) ≅
      (inverseImage (inclusion E)).obj A :=
  (((adjunction (inclusion V)).comp (adjunction (inclusionOfLE h))).leftAdjointUniq
    (show inverseImage (inclusion E) ⊣
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusionOfLE h) ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion V) from
      adjunction (inclusion E))).app A

variable {I : Type u} [Preorder I]

/-- Restriction of the ambient sheaf to each open stage.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
abbrev stageSheaf (V : I → Opens T)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (i : I) :=
  (inverseImage (inclusion (V i : Set T))).obj A

/-- The transition f-map, transposed from the unit-preserving composition isomorphism.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
def transition (V : I → Opens T) (hV : Antitone V)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (i j : I) (h : i ≤ j) : stageSheaf V A i ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusionOfLE (hV h))).obj
        (stageSheaf V A j) :=
  (adjunction (inclusionOfLE (hV h))).homEquiv _ _ (restrictionIso (hV h) A).hom

/-- On the common subspace the coefficient diagram is constant.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
abbrev coefficients (E : Set T)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :=
  (Functor.const I).obj ((inverseImage (inclusion E)).obj A)

/-- Each constant term identifies with the inverse image from its stage.
Source: Stacks Project, Sheaves on Spaces, inverse-image adjunction; Cohomology, Tag 0A37.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
def coefficientIso (V : I → Opens T) (E : Set T) (hE : ∀ i, E ⊆ V i)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (i : I) :
    (coefficients (I := I) E A).obj i ≅
      (inverseImage (inclusionOfLE (hE i))).obj (stageSheaf V A i) :=
  (restrictionIso (hE i) A).symm

private theorem transition_unit (V : I → Opens T) (hV : Antitone V)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (i j : I) (h : i ≤ j) :
    (adjunction (inclusion (V i : Set T))).unit.app A ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion (V i : Set T))).map
        (transition V hV A i j h) =
      (adjunction (inclusion (V j : Set T))).unit.app A := by
  unfold transition restrictionIso
  exact ((adjunction (inclusion (V i : Set T))).comp
    (adjunction (inclusionOfLE (hV h)))).homEquiv_leftAdjointUniq_hom_app
      (adjunction (inclusion (V j : Set T))) A

private theorem transition_self (V : I → Opens T) (hV : Antitone V)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (i : I) :
    transition V hV A i i le_rfl = 𝟙 (stageSheaf V A i) := by
  apply ((adjunction (inclusion (V i : Set T))).homEquiv _ _).injective
  exact (transition_unit V hV A i i le_rfl).trans
    ((adjunction (inclusion (V i : Set T))).homEquiv_id A).symm

private theorem transition_comp (V : I → Opens T) (hV : Antitone V)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) :
    transition V hV A i k (hij.trans hjk) = transition V hV A i j hij ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusionOfLE (hV hij))).map
        (transition V hV A j k hjk) := by
  apply ((adjunction (inclusion (V i : Set T))).homEquiv _ _).injective
  change (adjunction (inclusion (V i : Set T))).unit.app A ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion (V i : Set T))).map _ =
    (adjunction (inclusion (V i : Set T))).unit.app A ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion (V i : Set T))).map _
  rw [Functor.map_comp, ← Category.assoc, transition_unit V hV A i j hij]
  exact (transition_unit V hV A i k (hij.trans hjk)).trans
    (transition_unit V hV A j k hjk).symm

private theorem restriction_unit (E V : Set T) (h : E ⊆ V)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
    (adjunction (inclusion V)).unit.app A ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion V)).map
        ((adjunction (inclusionOfLE h)).unit.app ((inverseImage (inclusion V)).obj A) ≫
          (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusionOfLE h)).map
            (restrictionIso h A).hom) =
      (adjunction (inclusion E)).unit.app A := by
  unfold restrictionIso
  exact ((adjunction (inclusion V)).comp
    (adjunction (inclusionOfLE h))).homEquiv_leftAdjointUniq_hom_app
      (adjunction (inclusion E)) A

private theorem coefficient_unit (V : I → Opens T) (hV : Antitone V)
    (E : Set T) (hE : ∀ i, E ⊆ V i)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (i j : I) (h : i ≤ j) :
    (adjunction (inclusionOfLE (hE i))).unit.app (stageSheaf V A i) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusionOfLE (hE i))).map
        ((coefficientIso V E hE A i).inv ≫ (coefficientIso V E hE A j).hom) =
      transition V hV A i j h ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusionOfLE (hV h))).map
          ((adjunction (inclusionOfLE (hE j))).unit.app (stageSheaf V A j)) := by
  apply (cancel_mono ((TopCat.Sheaf.pushforward AddCommGrpCat.{u}
    (inclusionOfLE (hE i))).map (restrictionIso (hE j) A).hom)).mp
  simp only [coefficientIso, Iso.symm_inv, Iso.symm_hom, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
  apply ((adjunction (inclusion (V i : Set T))).homEquiv _ _).injective
  change (adjunction (inclusion (V i : Set T))).unit.app A ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion (V i : Set T))).map _ =
    (adjunction (inclusion (V i : Set T))).unit.app A ≫
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (inclusion (V i : Set T))).map _
  simp only [Functor.map_comp, ← Category.assoc]
  rw [transition_unit V hV A i j h]
  exact (restriction_unit E (V i) (hE i) A).trans
    (restriction_unit E (V j) (hE j) A).symm

/-- Restriction f-maps obey the system laws, and the inverse images form the specified
constant diagram on the common subspace. Source: Stacks Project, Cohomology, Tag 0A37,
restriction-system setup; Sheaves on Spaces, inverse-image adjunction.
(blueprint: lem-weil-pbc-open-system-restriction-presentation) -/
theorem restriction_presentation (V : I → Opens T) (hV : Antitone V)
    (E : Set T) (hE : ∀ i, E ⊆ V i)
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) :
    (∀ (i : I) (U : Opens (V i)) (s : (stageSheaf V A i).obj.obj (op U)),
      HEq ((transition V hV A i i le_rfl).hom.app (op U) s) s) ∧
    (∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
      (U : Opens (V i)) (s : (stageSheaf V A i).obj.obj (op U)),
      HEq ((transition V hV A i k (hij.trans hjk)).hom.app (op U) s)
        ((transition V hV A j k hjk).hom.app
          (op ((Opens.map (inclusionOfLE (hV hij))).obj U))
            ((transition V hV A i j hij).hom.app (op U) s))) ∧
    (∀ (i j : I) (h : i ≤ j) (U : Opens (V i))
      (s : (stageSheaf V A i).obj.obj (op U)),
      HEq (((coefficientIso V E hE A i).inv ≫
          (coefficients (I := I) E A).map (homOfLE h) ≫
          (coefficientIso V E hE A j).hom).hom.app
            (op ((Opens.map (inclusionOfLE (hE i))).obj U))
        (((adjunction (inclusionOfLE (hE i))).unit.app (stageSheaf V A i)).hom.app
          (op U) s))
        (((adjunction (inclusionOfLE (hE j))).unit.app (stageSheaf V A j)).hom.app
          (op ((Opens.map (inclusionOfLE (hV h))).obj U))
            ((transition V hV A i j h).hom.app (op U) s))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i U s
    exact heq_of_eq (congrArg (fun φ ↦ (φ.hom.app (op U)).hom s)
      (transition_self V hV A i))
  · intro i j k hij hjk U s
    exact heq_of_eq (congrArg (fun φ ↦ (φ.hom.app (op U)).hom s)
      (transition_comp V hV A i j k hij hjk))
  · intro i j h U s
    have hc := congrArg (fun φ ↦ (φ.hom.app (op U)).hom s)
      (coefficient_unit V hV E hE A i j h)
    exact heq_of_eq hc

end OpenSystem
end TopCat
