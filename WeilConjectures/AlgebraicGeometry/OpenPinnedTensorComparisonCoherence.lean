/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedTargetCounitTriangle
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSourceCounitTriangle

/-! # Counit comparison for one open leg
Source: Stacks Project, Tags 08DW and 0D5S. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
private theorem map_comparison_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).hom.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P := rfl

private theorem map_comparison_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H)
    (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso e (.up ℤ)).inv.app P =
      (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app P := rfl

private theorem lift_comparison
    {I C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive B] [Preadditive E]
    (T : I → C ⥤ E) [∀ i, (T i).Additive]
    (F : C ⥤ D) (G : D ⥤ E) (R : C ⥤ B) (J : B ⥤ E)
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    {i j : I} (h : i = j) (a : F ⋙ G ≅ T j) (b : R ⋙ J ≅ T i)
    (r : F ⋙ G ≅ R ⋙ J) (P : HomotopyCategory C (.up ℤ))
    (hb : a.inv ≫ r.hom = eqToHom (congrArg T h).symm ≫ b.inv) :
    (Functor.mapHomotopyCategoryCompIso a (.up ℤ)).inv.app P ≫
      (Functor.mapHomotopyCategoryCompIso r (.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm).hom.app P =
    eqToHom (congrArg (fun i ↦ ((T i).mapHomotopyCategory (.up ℤ)).obj P) h).symm ≫
      (Functor.mapHomotopyCategoryCompIso b (.up ℤ)).inv.app P := by
  cases h
  simp only [eqToHom_refl, Category.id_comp] at hb ⊢
  have hh := congrArg (fun t ↦ (NatTrans.mapHomotopyCategory t (.up ℤ)).app P) hb
  simp only [NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app] at hh
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, map_comparison_hom,
    map_comparison_inv, Iso.refl_inv, NatTrans.mapHomotopyCategory_id,
    NatTrans.id_app, Category.comp_id] using hh

variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

end AlgebraicGeometry
