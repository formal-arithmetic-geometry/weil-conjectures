/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

/-! Source: blueprint composition isomorphism and its canonicity and associativity. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
private lemma derived_iso_trans
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ≅ G) (d : G ≅ H) :
    Functor.mapDerivedCategoryNatIso (e ≪≫ d) =
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryNatIso d :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_trans e d)

private lemma derived_iso_symm
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    Functor.mapDerivedCategoryNatIso e.symm = (Functor.mapDerivedCategoryNatIso e).symm :=
  Iso.ext (Functor.mapDerivedCategoryNatIso_symm e)

private lemma derived_iso_eqToIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    Functor.mapDerivedCategoryNatIso (eqToIso h) = eqToIso (by subst h; rfl) := by
  subst h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

private lemma derived_triangle_assoc
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
    (FG : C₀ ⥤ C₂) (GH : C₁ ⥤ C₃) (FGH : C₀ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [FG.Additive] [GH.Additive] [FGH.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (eFG : FG ≅ F ⋙ G) (eGH : GH ≅ G ⋙ H)
    (eF_GH : FGH ≅ F ⋙ GH) (eFG_H : FGH ≅ FG ⋙ H)
    (h : eF_GH ≪≫ Functor.isoWhiskerLeft F eGH =
      eFG_H ≪≫ Functor.isoWhiskerRight eFG H) :
    (Functor.mapDerivedCategoryTriangleIso eF_GH).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryTriangleIso eGH).hom =
      (Functor.mapDerivedCategoryTriangleIso eFG_H).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eFG).hom
          H.mapDerivedCategory := by
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F GH).hom,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerLeft,
    Category.assoc, ← Category.assoc (Functor.mapDerivedCategoryCompIso FG H).hom,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerRight]
  simp only [← Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_trans, h,
    Functor.mapDerivedCategoryNatIso_trans]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_assoc]

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local irreducible] upperStar lowerStar
  Functor.mapDerivedCategory Functor.rightDerivedFunctor upperStarComp lowerStarComp
  upperStarLowerStarAdjunction Scheme.instCategory

private noncomputable def ordinaryComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    upperStar Λ fg ≅ upperStar Λ g ⋙ upperStar Λ f :=
  eqToIso (congrArg (upperStar Λ) hfg) ≪≫ upperStarComp Λ f g

private noncomputable def exactComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (upperStar Λ fg).mapDerivedCategory ≅
      (upperStar Λ g).mapDerivedCategory ⋙ (upperStar Λ f).mapDerivedCategory :=
  Functor.mapDerivedCategoryTriangleIso (ordinaryComp Λ f g fg hfg)

private lemma exactComp_assoc {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) :
    (exactComp Λ f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (exactComp Λ g h gh hgh).hom
          (upperStar Λ f).mapDerivedCategory =
      (exactComp Λ fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (upperStar Λ h).mapDerivedCategory
          (exactComp Λ f g fg hfg).hom := by
  have he : ordinaryComp Λ fg h fgh hfgh ≪≫
        Functor.isoWhiskerLeft (upperStar Λ h) (ordinaryComp Λ f g fg hfg) =
      ordinaryComp Λ f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc]) ≪≫
        Functor.isoWhiskerRight (ordinaryComp Λ g h gh hgh) (upperStar Λ f) := by
    subst hfg hgh hfgh
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [ordinaryComp, eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    simpa only [upperStarCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp, Category.assoc] using
      upperStarComp_hom_app_comp_upperStarComp_hom_app Λ f g h M
  exact (derived_triangle_assoc (upperStar Λ h) (upperStar Λ g) (upperStar Λ f)
    (upperStar Λ gh) (upperStar Λ fg) (upperStar Λ fgh)
    (ordinaryComp Λ g h gh hgh) (ordinaryComp Λ f g fg hfg)
    (ordinaryComp Λ fg h fgh hfgh)
    (ordinaryComp Λ f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])) he).symm

private noncomputable def exactSquare {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {j : Y' ⟶ Y} {f' : X' ⟶ Y'} {i : X' ⟶ X}
    (sq : CommSq i f' f j) :
    (upperStar Λ f).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory ≅
      (upperStar Λ j).mapDerivedCategory ⋙ (upperStar Λ f').mapDerivedCategory :=
  (exactComp Λ i f (i ≫ f) rfl).symm ≪≫ exactComp Λ f' j (i ≫ f) sq.w

private lemma exactSquare_vert {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {i : X' ⟶ X} {j : Y' ⟶ Y} {a : Z' ⟶ Z}
    (sqf : CommSq i f' f j) (sqg : CommSq j g' g a)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (exactSquare Λ (sqf.vert_comp sqg)).hom.app M =
      (upperStar Λ i).mapDerivedCategory.map
          ((exactComp Λ f g (f ≫ g) rfl).hom.app M) ≫
        (exactSquare Λ sqf).hom.app ((upperStar Λ g).mapDerivedCategory.obj M) ≫
        (upperStar Λ f').mapDerivedCategory.map ((exactSquare Λ sqg).hom.app M) ≫
        (exactComp Λ f' g' (f' ≫ g') rfl).inv.app
          ((upperStar Λ a).mapDerivedCategory.obj M) := by
  have h₁ := NatTrans.congr_app (exactComp_assoc Λ i f g (i ≫ f) (f ≫ g)
    (i ≫ (f ≫ g)) rfl rfl (Category.assoc i f g).symm) M
  have h₂ := NatTrans.congr_app (exactComp_assoc Λ f' j g (i ≫ f) (j ≫ g)
    (i ≫ (f ≫ g)) sqf.w rfl (Category.assoc i f g).symm) M
  have hd : i ≫ (f ≫ g) = (f' ≫ g') ≫ a := (sqf.vert_comp sqg).w
  have h₃ := NatTrans.congr_app (exactComp_assoc Λ f' g' a (f' ≫ g') (j ≫ g)
    (i ≫ (f ≫ g)) rfl sqg.w hd) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    at h₁ h₂ h₃
  rw [← cancel_epi ((exactComp Λ i (f ≫ g) (i ≫ (f ≫ g)) rfl).hom.app M)]
  simp only [exactSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, Iso.hom_inv_id_app_assoc, ← reassoc_of% h₂,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% h₃, Iso.hom_inv_id_app, Category.comp_id]

private lemma exactSquare_eq {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {j : Y' ⟶ Y} {f' : X' ⟶ Y'} {i : X' ⟶ X}
    (sq : CommSq i f' f j) :
    exactSquare Λ sq = (derivedOpenCoherencePullbackSquare Λ sq).symm := by
  apply Iso.ext
  simp only [exactSquare, exactComp, ordinaryComp, Functor.mapDerivedCategoryTriangleIso,
    derivedOpenCoherencePullbackSquare, openCoherencePullbackSquare,
    derived_iso_trans, derived_iso_symm, derived_iso_eqToIso, eqToIso_refl,
    Iso.refl_trans, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, eqToIso.hom, eqToIso.inv]

private lemma exactSquare_vert_inv {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    {i : X' ⟶ X} {j : Y' ⟶ Y} {a : Z' ⟶ Z}
    (sqf : CommSq i f' f j) (sqg : CommSq j g' g a) :
    (TwoSquare.vComp (derivedOpenCoherencePullbackSquare Λ sqg).hom
      (derivedOpenCoherencePullbackSquare Λ sqf).hom).whiskerLeft
        (exactComp Λ f g (f ≫ g) rfl).inv =
      TwoSquare.whiskerRight
        (derivedOpenCoherencePullbackSquare Λ (sqf.vert_comp sqg)).hom
        (exactComp Λ f' g' (f' ≫ g') rfl).inv := by
  ext M
  have h := exactSquare_vert Λ sqf sqg M
  have hf := congrArg Iso.inv (exactSquare_eq Λ sqf)
  have hg := congrArg Iso.inv (exactSquare_eq Λ sqg)
  have ho := congrArg Iso.inv (exactSquare_eq Λ (sqf.vert_comp sqg))
  simp only [Iso.symm_inv] at hf hg ho
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, ← hf, ← hg, ← ho, TwoSquare.natTrans]
  rw [← cancel_epi ((exactComp Λ f' g' (f' ≫ g') rfl).hom.app
    ((upperStar Λ a).mapDerivedCategory.obj M)),
    ← cancel_mono ((exactSquare Λ (sqf.vert_comp sqg)).hom.app M)]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  rw [h]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app]
  simp only [Functor.comp_obj]

end AlgebraicGeometry.ProEtale.CondensedRing
