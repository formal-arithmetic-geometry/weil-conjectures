/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeOpenUnit

/-! # Open component compatibility for derived base change

Source: Stacks Project, Tags 08HY, 08BV and 0DJ9.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section
namespace AlgebraicGeometry

theorem mate_naturality
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R') (P : C ⥤ C') (Q : D ⥤ D')
    (e : P ⋙ L' ≅ L ⋙ Q) {Y Z : D} (k : Y ⟶ Z) :
    P.map (R.map k) ≫
        a'.homEquiv _ _ (e.hom.app (R.obj Z) ≫ Q.map (a.counit.app Z)) =
      a'.homEquiv _ _ (e.hom.app (R.obj Y) ≫ Q.map (a.counit.app Y)) ≫
        R'.map (Q.map k) := by
  rw [← a'.homEquiv_naturality_left, ← a'.homEquiv_naturality_right]
  congr 1
  have hn := e.hom.naturality (R.map k)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← Q.map_comp]
  have hc := a.counit.naturality k
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc]

private theorem mate_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (a' : L' ⊣ R') (P : C ⥤ C') (Q : D ⥤ D')
    (e : P ⋙ L' ≅ L ⋙ Q) (K : C) (K' : C') (ψ : P.obj K ⟶ K') :
    P.map (a.unit.app K) ≫
        a'.homEquiv _ _ (e.hom.app (R.obj (L.obj K)) ≫
          Q.map (a.counit.app (L.obj K))) ≫
        R'.map (e.inv.app K ≫ L'.map ψ) = ψ ≫ a'.unit.app K' := by
  rw [← a'.homEquiv_naturality_right, ← a'.homEquiv_naturality_left]
  have ht :
      L'.map (P.map (a.unit.app K)) ≫
          (e.hom.app (R.obj (L.obj K)) ≫ Q.map (a.counit.app (L.obj K))) ≫
          (e.inv.app K ≫ L'.map ψ) = L'.map ψ := by
    simp only [← Category.assoc]
    have hn := e.hom.naturality (a.unit.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
    rw [hn]
    simp only [Category.assoc, ← Q.map_comp_assoc, a.left_triangle_components,
      Functor.id_obj, Functor.comp_obj,
      Q.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  rw [ht, Adjunction.homEquiv_unit, a'.unit_naturality]

private theorem mate_unit_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L A : C ⥤ D} {R : D ⥤ C} {L' A' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (ar : A ⊣ R) (a' : L' ⊣ R') (ar' : A' ⊣ R')
    (P : C ⥤ C') (Q : D ⥤ D') (e : P ⋙ L' ≅ L ⋙ Q)
    (K : C) (K' : C') (ψ : P.obj K ⟶ K') :
    let b := Functor.isoWhiskerLeft P (a'.leftAdjointUniq ar').symm ≪≫ e ≪≫
      Functor.isoWhiskerRight (a.leftAdjointUniq ar) Q
    P.map (ar.unit.app K) ≫
        a'.homEquiv _ _ (e.hom.app (R.obj (A.obj K)) ≫
          Q.map (a.counit.app (A.obj K))) ≫
        R'.map (b.inv.app K ≫ A'.map ψ) = ψ ≫ ar'.unit.app K' := by
  intro b
  let d := a.leftAdjointUniq ar
  let d' := a'.leftAdjointUniq ar'
  have hc : Q.map (d.hom.app K) ≫ b.inv.app K =
      e.inv.app K ≫ d'.hom.app (P.obj K) := by
    simp only [b, d, d', Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
      ← Q.map_comp_assoc, Iso.hom_inv_id_app, Q.map_id, Category.id_comp]
  rw [← Adjunction.unit_leftAdjointUniq_hom_app a ar K]
  simp only [P.map_comp, Category.assoc, Functor.comp_obj, Functor.id_obj]
  have hm := mate_naturality a a' P Q e ((a.leftAdjointUniq ar).hom.app K)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hm
  rw [← Category.assoc (P.map (R.map ((a.leftAdjointUniq ar).hom.app K))), hm]
  simp only [Category.assoc, ← R'.map_comp]
  have hn := d'.hom.naturality ψ
  change P.map (a.unit.app K) ≫
      a'.homEquiv _ _ (e.hom.app (R.obj (L.obj K)) ≫
        Q.map (a.counit.app (L.obj K))) ≫
      R'.map (Q.map (d.hom.app K) ≫ b.inv.app K ≫ A'.map ψ) = _
  rw [← Category.assoc (Q.map (d.hom.app K)), hc, Category.assoc, ← hn]
  simp only [R'.map_comp, ← Category.assoc, Functor.comp_obj, Functor.id_obj]
  have hm := mate_unit a a' P Q e K K' ψ
  simp only [Functor.comp_obj, Functor.id_obj, R'.map_comp, ← Category.assoc] at hm
  rw [hm]
  rw [Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app a' ar' K']

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
