/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Equivalence
/-! # Inverse coefficient-comparison coordinates

Source: blueprint sk-thm-sf-tensor-hom Complement, coefficient cancellation.
(blueprint: lem-sf-inverse-comparison-coordinates).
-/
@[expose] public section
set_option autoImplicit false
open CategoryTheory
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']

/-- Cancel the prescribed inverse comparison against its original coordinates.

Source: blueprint sk-thm-sf-tensor-hom Complement, second normalization.
(blueprint: lem-sf-inverse-comparison-coordinates).
Proof: expand the equivalence cancellation isomorphisms. The triangle identity
replaces the source unit by the inverse image of its counit. Naturality of cmp
then cancels cmp inverse with cmp. Naturality of the target counit gives the result. -/
theorem CategoryTheory.inverseComparison_coordinates
    (qX : C ≌ C') (qY : D ≌ D') (S : C ⥤ D) (P : C' ⥤ D')
    (cmp : qX.inverse ⋙ S ≅ P ⋙ qY.inverse)
    (M : C') (N : D') (v : P.obj M ⟶ N) :
    let s : S ⋙ qY.functor ≅ qX.functor ⋙ P :=
      (Iso.inverseCompIso
        ((Iso.compInverseIso (H := qY.symm) cmp).symm ≪≫
          Functor.associator _ _ _) (G := qX.symm)).symm
    s.inv.app (qX.inverse.obj M) ≫ qY.functor.map
        (cmp.hom.app M ≫ qY.inverse.map v) =
      P.map (qX.counitIso.hom.app M) ≫ v ≫ qY.counitIso.inv.app N := by
  dsimp only
  simp only [Iso.symm_inv, Iso.inverseCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app,
    Iso.compInverseIso, Iso.symm_hom, Iso.trans_inv, Functor.rightUnitor_inv_app,
    Functor.comp_obj, Equivalence.symm_counitIso, Equivalence.symm_unitIso,
    Equivalence.symm_functor, Equivalence.symm_inverse,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  erw [Category.id_comp]
  change qY.counitIso.inv.app _ ≫
    qY.functor.map (cmp.inv.app _) ≫
      qY.functor.map (S.map (qX.unitIso.inv.app (qX.inverse.obj M))) ≫
        qY.functor.map (cmp.hom.app M) ≫ qY.functor.map (qY.inverse.map v) = _
  rw [qX.unitInv_app_inverse M]
  have hnat := cmp.hom.naturality (qX.counitIso.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnat
  change S.map (qX.inverse.map (qX.counit.app M)) ≫ cmp.hom.app M = _ at hnat
  rw [← qY.functor.map_comp_assoc, ← qY.functor.map_comp_assoc,
    Category.assoc, hnat]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  simp only [Category.assoc]
  change qY.counitIso.inv.app _ ≫ qY.functor.map (qY.inverse.map
    (P.map (qX.counitIso.hom.app M))) ≫ qY.functor.map (qY.inverse.map v) = _
  rw [← qY.functor.map_comp, ← qY.inverse.map_comp]
  simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
    (qY.counitIso.inv.naturality (P.map (qX.counitIso.hom.app M) ≫ v)).symm
