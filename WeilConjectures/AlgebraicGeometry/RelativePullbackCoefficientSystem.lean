/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeDirectImageSheafLimit
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.SixFunctors.BaseChange.Pasting
import Mathlib.CategoryTheory.Filtered.Final

/-! # The coefficient system pulled back from a fixed stage

Source: Stacks Tag 0GIU, the single-sheaf case, and Tag 0EYM.
(blueprint: lem-sf-relative-pullback-coefficient-system).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar

instance relativeTail_isDirected {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (i₀ : I) : IsDirected (Set.Ici i₀) (· ≤ ·) where
  directed i j := by
    obtain ⟨k, hi, hj⟩ := directed_of (· ≤ ·) i.val j.val
    exact ⟨⟨k, i.property.trans hi⟩, hi, hj⟩

/-- The tail inclusion is final in a directed preorder.

Proof: every index has an upper bound with the fixed index; a directed preorder
satisfies the connectedness criterion for a final monotone functor.
Source: Stacks Tag 0GIU, restriction to the tail.
(blueprint: lem-sf-relative-pullback-coefficient-system). -/
theorem relativeTail_final {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I) :
    (Subtype.mono_coe (· ∈ Set.Ici i₀)).functor.Final := by
  rw [Monotone.final_functor_iff]
  intro i
  obtain ⟨j, h₀, hi⟩ := directed_of (· ≤ ·) i₀ i
  exact ⟨⟨j, h₀⟩, hi⟩

private lemma pullback_inv_comp {R S T V : Scheme.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ V)
    (fg : R ⟶ T) (gh : S ⟶ V) (fgh : R ⟶ V)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} fg h fgh hfgh).inv.app F =
      (upperStarComp AddCommGrpCat.{u + 1} f g fg hfg).hom.app
          ((upperStar AddCommGrpCat.{u + 1} h).obj F) ≫
        (upperStar AddCommGrpCat.{u + 1} f).map
          ((upperStarComp AddCommGrpCat.{u + 1} g h gh hgh).inv.app F) ≫
        (upperStarComp AddCommGrpCat.{u + 1} f gh fgh
          (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app F := by
  have H := NatTrans.congr_app (upperStarComp_assoc' AddCommGrpCat.{u + 1}
    f g h fg gh fgh hfg hgh hfgh) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at H
  have H' := congrArg Iso.inv (Iso.ext H :
    (upperStarComp AddCommGrpCat.{u + 1} f gh fgh
        (by rw [hfgh, hfg, hgh, Category.assoc])).app F ≪≫
      (upperStar AddCommGrpCat.{u + 1} f).mapIso
        ((upperStarComp AddCommGrpCat.{u + 1} g h gh hgh).app F) =
    (upperStarComp AddCommGrpCat.{u + 1} fg h fgh hfgh).app F ≪≫
      (upperStarComp AddCommGrpCat.{u + 1} f g fg hfg).app
        ((upperStar AddCommGrpCat.{u + 1} h).obj F))
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv] at H'
  have H'' := congrArg (fun k ↦
    (upperStarComp AddCommGrpCat.{u + 1} f g fg hfg).hom.app
      ((upperStar AddCommGrpCat.{u + 1} h).obj F) ≫ k) H'
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using H''.symm

/-- Fixed-stage coefficient sheaves on the directed tail. -/
noncomputable abbrev relativePullbackSheaf
    {I : Type u} [Preorder I] (DU : Iᵒᵖ ⥤ Scheme.{u}) (i₀ : I)
    (F : Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (i : Set.Ici i₀) :=
  (upperStar AddCommGrpCat.{u + 1}
    (DU.map (homOfLE i.property : i₀ ⟶ i.val).op)).obj F

/-- Canonical transitions of a fixed-stage sheaf coefficient system. -/
noncomputable def relativePullbackSheafMap
    {I : Type u} [Preorder I] (DU : Iᵒᵖ ⥤ Scheme.{u}) (i₀ : I)
    (F : Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1})
    {i j : Set.Ici i₀} (h : i ⟶ j) :
    (upperStar AddCommGrpCat.{u + 1}
      (DU.map (homOfLE (leOfHom h) : i.val ⟶ j.val).op)).obj
        (relativePullbackSheaf DU i₀ F i) ⟶ relativePullbackSheaf DU i₀ F j :=
  (upperStarComp AddCommGrpCat.{u + 1}
    (DU.map (homOfLE (leOfHom h) : i.val ⟶ j.val).op)
    (DU.map (homOfLE i.property : i₀ ⟶ i.val).op)
    (DU.map (homOfLE j.property : i₀ ⟶ j.val).op)
    (by rw [← DU.map_comp]; congr 1)).inv.app F

private lemma pullback_inv_id_transport {X Y : Scheme.{u}}
    (f : X ⟶ X) (hf : f = 𝟙 X) (g : X ⟶ Y) (h : g = f ≫ g)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (upperStarComp AddCommGrpCat.{u + 1} f g g h).inv.app F =
      eqToHom (congrArg (fun k ↦ (upperStar AddCommGrpCat.{u + 1} k).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj F)) hf) ≫
      (upperStarId AddCommGrpCat.{u + 1} X).hom.app
        ((upperStar AddCommGrpCat.{u + 1} g).obj F) := by
  subst f
  simp [upperStarComp_id_left]

/-- The identity law for fixed-stage sheaf transitions. -/
lemma relativePullbackSheafMap_id
    {I : Type u} [Preorder I] (DU : Iᵒᵖ ⥤ Scheme.{u}) (i₀ : I)
    (F : Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (i : Set.Ici i₀) :
    relativePullbackSheafMap DU i₀ F (𝟙 i) =
      eqToHom (congrArg (fun f ↦ (upperStar AddCommGrpCat.{u + 1} f).obj
        (relativePullbackSheaf DU i₀ F i)) (DU.map_id (op i.val))) ≫
      (upperStarId AddCommGrpCat.{u + 1} (DU.obj (op i.val))).hom.app
        (relativePullbackSheaf DU i₀ F i) := by
  exact pullback_inv_id_transport _ (DU.map_id (op i.val)) _ _ F

/-- The composition law for fixed-stage sheaf transitions. -/
lemma relativePullbackSheafMap_comp
    {I : Type u} [Preorder I] (DU : Iᵒᵖ ⥤ Scheme.{u}) (i₀ : I)
    (F : Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (i j k : Set.Ici i₀) (h : i ⟶ j) (h' : j ⟶ k) :
    relativePullbackSheafMap DU i₀ F (h ≫ h') =
      (upperStarComp AddCommGrpCat.{u + 1}
        (DU.map (homOfLE (leOfHom h') : j.val ⟶ k.val).op)
        (DU.map (homOfLE (leOfHom h) : i.val ⟶ j.val).op)
        (DU.map (homOfLE (leOfHom (h ≫ h')) : i.val ⟶ k.val).op)
        (by rw [← DU.map_comp]; congr 1)).hom.app (relativePullbackSheaf DU i₀ F i) ≫
      (upperStar AddCommGrpCat.{u + 1}
        (DU.map (homOfLE (leOfHom h') : j.val ⟶ k.val).op)).map
          (relativePullbackSheafMap DU i₀ F h) ≫ relativePullbackSheafMap DU i₀ F h' := by
  exact pullback_inv_comp _ _ _ _ _ _ _ _ _ F

/-- The coefficient diagram pulled from one fixed stage has its expected colimit.

Proof: the inverse-image composition isomorphisms identify every pulled-back
coefficient with the pullback from the fixed stage. Associativity identifies all
transition maps under these isomorphisms. The resulting cocone has isomorphic legs,
and the tail is connected, so it is a colimit cocone. Uniqueness of colimits gives
the stated isomorphism, with the stated formula on every leg.
Source: Stacks Tag 0GIU, the constant coefficient diagram in the sheaf case.
(blueprint: lem-sf-relative-pullback-coefficient-system). -/
theorem relativePullbackSheaf_colimit
    {I : Type u} [Preorder I] (DU : Iᵒᵖ ⥤ Scheme.{u}) (cU : Cone DU) (i₀ : I)
    [IsConnected (Set.Ici i₀)]
    (F : Sheaf (DU.obj (op i₀)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (C : Set.Ici i₀ ⥤ Sheaf cU.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (e : ∀ i : Set.Ici i₀, C.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i.val))).obj
        (relativePullbackSheaf DU i₀ F i))
    (cF : Cocone C) (hcF : IsColimit cF)
    (hC : ∀ (i j : Set.Ici i₀) (h : i ⟶ j), C.map h =
      (e i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cU.π.app (op j.val))
          (DU.map (homOfLE (leOfHom h) : i.val ⟶ j.val).op)
          (cU.π.app (op i.val)) (cU.w _).symm).hom.app (relativePullbackSheaf DU i₀ F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op j.val))).map
          (relativePullbackSheafMap DU i₀ F h) ≫ (e j).inv) :
    ∃ eLimit : cF.pt ≅ (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i₀))).obj F,
      ∀ i : Set.Ici i₀, (e i).inv ≫ cF.ι.app i ≫ eLimit.hom =
        (upperStarComp AddCommGrpCat.{u + 1} (cU.π.app (op i.val))
          (DU.map (homOfLE i.property : i₀ ⟶ i.val).op)
          (cU.π.app (op i₀)) (cU.w _).symm).inv.app F := by
  let legIso (i : Set.Ici i₀) :=
    (upperStarComp AddCommGrpCat.{u + 1} (cU.π.app (op i.val))
      (DU.map (homOfLE i.property : i₀ ⟶ i.val).op)
      (cU.π.app (op i₀)) (cU.w _).symm).inv.app F
  let z : Cocone C :=
    { pt := (upperStar AddCommGrpCat.{u + 1} (cU.π.app (op i₀))).obj F
      ι :=
        { app := fun i ↦ (e i).hom ≫ legIso i
          naturality := fun i j h ↦ by
            change C.map h ≫ ((e j).hom ≫ legIso j) = ((e i).hom ≫ legIso i) ≫ 𝟙 _
            rw [hC, Category.comp_id]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            dsimp only [legIso, relativePullbackSheafMap]
            congr 1
            exact (pullback_inv_comp _ _ _ _ _ _ _ _ _ F).symm } }
  have : ∀ i, IsIso (z.ι.app i) := fun _ ↦ by dsimp [z, legIso]; infer_instance
  have : IsIso z.ι := NatIso.isIso_of_isIso_app _
  have hz : IsColimit z := z.isColimitOfIsIsoColimMapι
  refine ⟨hcF.coconePointUniqueUpToIso hz, ?_⟩
  intro i
  rw [hcF.comp_coconePointUniqueUpToIso_hom]
  exact (e i).inv_hom_id_assoc (legIso i)

end AlgebraicGeometry.Etale
