/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods
import Mathlib.RingTheory.SimpleRing.Field

/-! # The generic residue field as an affine-neighbourhood limit

Source: Stacks Project, Tag 0GK7, the reduced generic local-ring observation;
Tags 0GWT and 01YW for the affine-neighbourhood limit.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The spectrum of a component's generic residue field is the limit of the affine
neighbourhoods of that point on a reduced scheme.
Source: Stacks Project, Tag 0GK7, the generic local ring of the reduced affine base;
Tags 0GWT and 01YW, the stalk-spectrum limit.
Private comparison for the public affine-limit construction.

Proof: Affine neighbourhoods are nonempty and any two have a common smaller affine
neighbourhood. Thus their inclusion preorder is cofiltered. At a generic point of an
irreducible component of a reduced scheme the stalk is a field. Its residue map is
surjective and injective, hence an isomorphism. The known stalk-spectrum limit gives
a limiting cone on the affine neighbourhoods. Its vertex is therefore isomorphic to
the residue-field spectrum. For any cone as in the statement, cancelling the open
inclusions identifies all its legs with those of this limiting cone under the supplied
vertex isomorphism. Transporting the limit along this cone isomorphism proves the claim.
No integral or Noetherian hypothesis on the whole base is needed. -/
private theorem generic_residue_field_limit_of_vertex_iso
    (S : Scheme.{u}) [IsReduced S] (η : S)
    (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z) :
    let N := {U : S.Opens // IsAffineOpen U ∧ η ∈ U}
    let D : N ⥤ Scheme.{u} :=
      (show Monotone (fun U : N ↦ U.1) from fun _ _ h ↦ h).functor ⋙
        S.restrictFunctor ⋙ Over.forget S
    IsCofiltered N ∧
      ∀ (c : Cone D) (e : c.pt ≅ Spec (S.residueField η)),
        (∀ U : N, c.π.app U ≫ U.1.ι = e.hom ≫ S.fromSpecResidueField η) →
          Nonempty (IsLimit c) := by
  classical
  dsimp only
  let N := {U : S.Opens // IsAffineOpen U ∧ η ∈ U}
  let D : N ⥤ Scheme.{u} :=
    (show Monotone (fun U : N ↦ U.1) from fun _ _ h ↦ h).functor ⋙
      S.restrictFunctor ⋙ Over.forget S
  have : Nonempty N := by
    obtain ⟨U, hU, hηU, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := S) (x := η) (U := ⊤) (by trivial)
    exact ⟨⟨U, hU, hηU⟩⟩
  have : IsDirected N (· ≥ ·) := ⟨fun U V ↦ by
    obtain ⟨W, hW, hηW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
      (show η ∈ U.1 ⊓ V.1 from ⟨U.2.2, V.2.2⟩)
    exact ⟨⟨W, hW, hηW⟩, hWUV.trans inf_le_left, hWUV.trans inf_le_right⟩⟩
  refine ⟨inferInstance, ?_⟩
  intro c e hcomm
  obtain ⟨Z, hZ, hηZ⟩ := hη
  have hf : IsField (S.presheaf.stalk η) :=
    isField_stalk_of_closure_mem_irreducibleComponents S η (hηZ.symm ▸ hZ)
  have : IsSimpleRing (S.presheaf.stalk η) := (isSimpleRing_iff_isField _).mpr hf
  have : IsIso (S.residue η) := (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(S.residue η).hom.injective, IsLocalRing.residue_surjective⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, huniv⟩ :=
    S.fromSpecStalk_limit_affine_neighbourhoods η
  let s : Cone D :=
    { pt := Spec (S.presheaf.stalk η)
      π :=
        { app := fun U ↦ U.1.fromSpecStalkOfMem η U.2.2
          naturality := by
            intro U V a
            apply (cancel_mono V.1.ι).mp
            simp [D] } }
  have hx (t : Cone D) : ∃! g : t.pt ⟶ Spec (S.presheaf.stalk η),
      ∀ U : N, g ≫ U.1.fromSpecStalkOfMem η U.2.2 = t.π.app U := by
    apply huniv t.pt (fun U ↦ t.π.app U)
    intro U V hVU
    exact t.w (homOfLE hVU)
  let hs : IsLimit s :=
    { lift := fun t ↦ (hx t).choose
      fac := fun t U ↦ (hx t).choose_spec.1 U
      uniq := fun t g hg ↦ (hx t).choose_spec.2 g hg }
  let ec : c ≅ s := Cone.ext (e ≪≫ asIso (Spec.map (S.residue η))) (by
    intro U
    apply (cancel_mono U.1.ι).mp
    simpa only [s, Iso.trans_hom, asIso_hom, Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.fromSpecResidueField] using hcomm U)
  exact ⟨hs.ofIsoLimit ec.symm⟩

/-- A limiting affine-neighbourhood cone with vertex isomorphic to the generic residue field.
Source: Stacks Project, Tags 0GK7, 0GWT and 01YW.
(blueprint: lem-weil-pbc-generic-residue-field-affine-limit)

Proof: Affine neighbourhoods form a cofiltered preorder. Construct the cone whose legs
are the residue-field spectrum map followed by the canonical stalk-to-neighbourhood
maps. Their composites with the open inclusions are the canonical residue-field point
of S, so the legs are natural by cancellation of those open immersions. The stalk is
a field at the given generic point since S is reduced. Thus its residue map is an
isomorphism, and the stalk-spectrum limit identifies the displayed cone as limiting,
as proved by the private vertex-isomorphism comparison. -/
theorem generic_residue_field_affine_limit
    (S : Scheme.{u}) [IsReduced S] (η : S)
    (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z) :
    let N := {U : S.Opens // IsAffineOpen U ∧ η ∈ U}
    let D : N ⥤ Scheme.{u} :=
      (show Monotone (fun U : N ↦ U.1) from fun _ _ h ↦ h).functor ⋙
        S.restrictFunctor ⋙ Over.forget S
    IsCofiltered N ∧
      ∃ (c : Cone D) (e : c.pt ≅ Spec (S.residueField η)),
        (∀ U : N, c.π.app U ≫ U.1.ι = e.hom ≫ S.fromSpecResidueField η) ∧
          Nonempty (IsLimit c) := by
  classical
  dsimp only
  let N := {U : S.Opens // IsAffineOpen U ∧ η ∈ U}
  let D : N ⥤ Scheme.{u} :=
    (show Monotone (fun U : N ↦ U.1) from fun _ _ h ↦ h).functor ⋙
      S.restrictFunctor ⋙ Over.forget S
  let c : Cone D :=
    { pt := Spec (S.residueField η)
      π :=
        { app := fun U ↦ Spec.map (S.residue η) ≫ U.1.fromSpecStalkOfMem η U.2.2
          naturality := by
            intro U V a
            apply (cancel_mono V.1.ι).mp
            simp [D] } }
  have hcomm (U : N) : c.π.app U ≫ U.1.ι =
      (Iso.refl _).hom ≫ S.fromSpecResidueField η := by
    simp [c, Scheme.fromSpecResidueField]
  have h := generic_residue_field_limit_of_vertex_iso S η hη
  exact ⟨h.1, c, Iso.refl _, hcomm, h.2 c (Iso.refl _) hcomm⟩

end AlgebraicGeometry
