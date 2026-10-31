/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! Identity specialization of the RootCoordinateFace exchange.

This is the identity-mate calculation needed by the smooth base-change exchange
compatibility theorem.  The calculation expands the normalized square comparison,
uses the two unit laws for `upperStarComp`, and cancels the two adjunction triangles.
(blueprint: lem-sbc-exchange-identity)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derived_transport
    {A B I : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : I → A ⥤ B) [∀ j, (F j).Additive]
    [∀ j, PreservesFiniteLimits (F j)] [∀ j, PreservesFiniteColimits (F j)]
    {j k : I} (h : j = k) :
    Functor.mapDerivedCategoryNatIso (eqToIso (congrArg F h)) =
      eqToIso (congrArg (fun j ↦ (F j).mapDerivedCategory) h) := by
  cases h
  exact Iso.ext Functor.mapDerivedCategoryNatIso_refl

private theorem derived_identity_square {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (I : C ⥤ C) (J : D ⥤ D)
    [F.Additive] [I.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (i : I ≅ 𝟭 C) (j : J ≅ 𝟭 D) :
    Functor.mapDerivedCategorySquareIso
        (Functor.isoWhiskerRight i F ≪≫ F.leftUnitor ≪≫
          F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F j.symm) =
      Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso i ≪≫ Functor.mapDerivedCategoryIdIso C)
          F.mapDerivedCategory ≪≫
        F.mapDerivedCategory.leftUnitor ≪≫ F.mapDerivedCategory.rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso j ≪≫ Functor.mapDerivedCategoryIdIso D).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hi := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight i F) K
  have hj := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F j.symm) K
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) K
  have hv := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) K
  have hleft : (Functor.mapDerivedCategoryNatIso F.leftUnitor).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hright : (Functor.mapDerivedCategoryNatIso F.rightUnitor.symm).hom = 𝟙 _ :=
    Functor.mapDerivedCategoryNatIso_refl
  have hv' : (Functor.mapDerivedCategoryCompIso F (𝟭 D)).hom.app K =
      (Functor.mapDerivedCategoryIdIso D).inv.app (F.mapDerivedCategory.obj K) := by
    apply (cancel_mono ((Functor.mapDerivedCategoryIdIso D).hom.app _)).mp
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app,
      Functor.comp_obj, Functor.id_obj, Iso.inv_hom_id_app] using hv
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app] at hi hj hu
  simp only [Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_trans,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, hleft, hright, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Functor.map_comp,
    Category.id_comp, Category.assoc]
  erw [Category.id_comp]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso I F).hom.app K)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [hj, ← reassoc_of% hi, reassoc_of% hu, hv']
  simp only [Functor.mapDerivedCategoryNatIso_symm]
  erw [Category.id_comp]

private theorem identity_mate {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
    (I : C ⥤ C) (J : D ⥤ D) (i : I ≅ 𝟭 C) (j : J ≅ 𝟭 D)
    (s : I ⋙ F ≅ F ⋙ J)
    (hs : s = Functor.isoWhiskerRight i F ≪≫ F.leftUnitor ≪≫
      F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F j.symm) (K : D) :
    (mateEquiv adj adj (TwoSquare.mk _ _ _ _ s.hom)).natTrans.app K =
      i.hom.app (G.obj K) ≫ G.map (j.inv.app K) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [CategoryTheory.Adjunction.homEquiv_counit,
    CategoryTheory.Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  rw [hs]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, TwoSquare.mk,
    Category.id_comp]
  erw [Category.id_comp]
  simp only [Category.assoc]
  simp only [Functor.map_comp, Category.assoc]
  have hc := adj.counit.naturality (j.inv.app K)
  simp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc]
  have hn := congrArg (F.map (i.hom.app _) ≫ ·)
    (j.inv.naturality (adj.counit.app K)).symm
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    Functor.comp_obj, Functor.id_obj, Functor.id_map, Category.assoc] using hn

private theorem iso_transport_loop {C : Type*} [Category C] {A B D : C}
    (p : B = A) (q : B = D) (r : D = A) :
    (eqToIso p).symm ≪≫ eqToIso q ≪≫ eqToIso r = Iso.refl A := by
  cases p
  cases q
  simp

private theorem ordinary_square_identity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : (𝟙 X) ≫ f = f ≫ (𝟙 Y)) :
  (CondensedRing.upperStarComp Λ f (𝟙 Y)).symm ≪≫
      eqToIso (congrArg (CondensedRing.upperStar Λ) h.symm) ≪≫
        CondensedRing.upperStarComp Λ (𝟙 X) f =
      Functor.isoWhiskerRight (CondensedRing.upperStarId Λ Y)
          (CondensedRing.upperStar Λ f) ≪≫
        (CondensedRing.upperStar Λ f).leftUnitor ≪≫
        (CondensedRing.upperStar Λ f).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (CondensedRing.upperStar Λ f)
          (CondensedRing.upperStarId Λ X).symm := by
  rw [CondensedRing.upperStarComp_id_left, CondensedRing.upperStarComp_id_right]
  have he : (CondensedRing.upperStarCongr Λ (Category.comp_id f)).symm ≪≫
      eqToIso (congrArg (CondensedRing.upperStar Λ) h.symm) ≪≫
        CondensedRing.upperStarCongr Λ (Category.id_comp f) =
      Iso.refl (CondensedRing.upperStar Λ f) := by
    exact iso_transport_loop
      (congrArg (CondensedRing.upperStar Λ) (Category.comp_id f))
      (congrArg (CondensedRing.upperStar Λ) h.symm)
      (congrArg (CondensedRing.upperStar Λ) (Category.id_comp f))
  have hh := congrArg (fun t ↦
    Functor.isoWhiskerRight (CondensedRing.upperStarId Λ Y)
        (CondensedRing.upperStar Λ f) ≪≫
      (CondensedRing.upperStar Λ f).leftUnitor ≪≫ t ≪≫
      (CondensedRing.upperStar Λ f).rightUnitor.symm ≪≫
      Functor.isoWhiskerLeft (CondensedRing.upperStar Λ f)
        (CondensedRing.upperStarId Λ X).symm) he
  simpa only [Iso.trans_symm, Functor.isoWhiskerRight_symm, Iso.symm_symm_eq,
    Iso.trans_assoc, Iso.refl_trans] using hh

private theorem derived_square_identity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : (𝟙 X) ≫ f = f ≫ (𝟙 Y)) :
    RootCoordinateFace.squareUpper Λ (𝟙 X) f f (𝟙 Y) h =
      Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ Y) ≪≫
          Functor.mapDerivedCategoryIdIso _) (RootCoordinateFace.upper Λ f) ≪≫
        (RootCoordinateFace.upper Λ f).leftUnitor ≪≫
        (RootCoordinateFace.upper Λ f).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (RootCoordinateFace.upper Λ f)
          (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
            Functor.mapDerivedCategoryIdIso _).symm := by
  let iY := Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ Y) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let iX := Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let a := CondensedRing.upperStarComp Λ f (𝟙 Y)
  let b := CondensedRing.upperStarComp Λ (𝟙 X) f
  let e := eqToIso (congrArg (CondensedRing.upperStar Λ) h.symm)
  have ho := ordinary_square_identity Λ f h
  have hs₀ : RootCoordinateFace.squareUpper Λ (𝟙 X) f f (𝟙 Y) h =
      Functor.mapDerivedCategorySquareIso (a.symm ≪≫ e ≪≫ b) := by
    apply Iso.ext
    simp only [RootCoordinateFace.squareUpper, RootCoordinateFace.upperComp,
      Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_trans,
      Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Category.assoc]
    rw [show Functor.mapDerivedCategoryNatIso e =
      eqToIso (congrArg (RootCoordinateFace.upper Λ) h.symm) from
        derived_transport (CondensedRing.upperStar Λ) h.symm]
  have hs : RootCoordinateFace.squareUpper Λ (𝟙 X) f f (𝟙 Y) h =
      Functor.isoWhiskerRight iY (RootCoordinateFace.upper Λ f) ≪≫
        (RootCoordinateFace.upper Λ f).leftUnitor ≪≫
        (RootCoordinateFace.upper Λ f).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (RootCoordinateFace.upper Λ f) iX.symm := by
    rw [hs₀, ho]
    exact derived_identity_square _ _ _ _ _
  exact hs

/-- The exchange for the square with identity vertical sides is the normalized
identity pullback on both ends.

Source: blueprint `sk-lem-sbc-exchange-compatibility`, formal identity clause.
Proof: expand the mate defining `RootCoordinateFace.exchange`; rewrite the two
identity composition comparisons with `upperStarComp_id_left` and
`upperStarComp_id_right`; apply the unit naturality and the counit triangle of
`RootCoordinateFace.adjunction`; finally identify the derived identity maps by
`Functor.mapDerivedCategoryIdIso`.
(blueprint: lem-sbc-exchange-identity)
-/
theorem sbcExchangeIdentity
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sq : ChosenCartesianSquare (𝟙 X) f f (𝟙 Y))
    (K : DerivedCategory (RootCoordinateFace.Modules Λ X)) :
    (RootCoordinateFace.exchange Λ (𝟙 X) f f (𝟙 Y) sq.w).app K =
      (Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ Y) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          ((RootCoordinateFace.lower Λ f).obj K) ≫
        (RootCoordinateFace.lower Λ f).map
          ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
            Functor.mapDerivedCategoryIdIso _).inv.app K) := by
  let iY := Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ Y) ≪≫
    Functor.mapDerivedCategoryIdIso _
  let iX := Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarId Λ X) ≪≫
    Functor.mapDerivedCategoryIdIso _
  exact identity_mate _ _ (RootCoordinateFace.adjunction Λ f) _ _ iY iX _
    (derived_square_identity Λ f sq.w) K

end AlgebraicGeometry.Scheme
