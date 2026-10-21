/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q7, P1
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import all Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import all Sheaf.CategoryTheory.RingedSiteDualityMaps
import Sheaf.Algebra.Homology.SignedDoubleHomCone

/-! # The degree-one shift equation for coefficient bidual evaluation

Source: Stacks Project, sites-cohomology.tex, Tags 0A97 and 08JC.
(blueprint: lem-coef-bidual-evaluation-shift-one).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.RingedHomUniverses

attribute [local irreducible] CategoryTheory.homComplexFunctor
  WeilConjectures.coefficientHomResolution CategoryTheory.ringedSiteDualityUnitComplex
  CategoryTheory.ringedSiteBidualDegree CategoryTheory.ringedSiteBidualComponent
namespace CategoryTheory
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Sheaf J CommRingCat.{max c v r})
private theorem generalHom_d_eval
    (E F : RingedSiteComplex.{c, v, r} J R) (n m p s t p' : ℤ)
    (hnm : n + 1 = m) (hps : p + n = s) (hpt : p + m = t) (hp' : p' + n = t)
    (U : Cᵒᵖ)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E F).X n).val.obj U)
    (W : (Over U.unop)ᵒᵖ) (x : (E.X p).val.obj (op W.unop.left)) :
    (((homComplexπ.{c, v, max c v r, max c v r} (R := R) E F m p t hpt).val.app U
      (((homComplex.{c, v, max c v r, max c v r} (R := R) E F).d n m).val.app U φ)).app W).hom x =
      (F.d s t).val.app (op W.unop.left)
        ((((homComplexπ.{c, v, max c v r, max c v r} (R := R) E F n p s hps).val.app U
          φ).app W).hom x) -
        n.negOnePow •
          (show (F.X t).val.obj (op W.unop.left) from
            ((((homComplexπ.{c, v, max c v r, max c v r} (R := R) E F n p' t hp').val.app U
              φ).app W).hom ((E.d p p').val.app (op W.unop.left) x))) := by
  let e : (((homComplex.{c, v, max c v r, max c v r} (R := R) E F).X n) ⟶
      SheafOfModules.homObj (R := R) (E.X p) (F.X t)) →+ (F.X t).val.obj (op W.unop.left) :=
    { toFun f := ((f.val.app U φ).app W).hom x
      map_zero' := rfl
      map_add' _ _ := rfl }
  have he := congrArg e
    (homComplex_d_π.{c, v, max c v r, max c v r} (J := J) (R := R) E F
      n m p t s p' hnm hpt hps hp')
  simp only [map_sub, Units.smul_def, map_zsmul] at he
  exact he
private theorem generalBidualSigns {G : Type*} [AddCommGroup G]
    (i q : ℤ) (x y : G) :
    (i * q).negOnePow • x -
      i.negOnePow • ((i * (q + 1)).negOnePow • (x - q.negOnePow • y)) =
        ((i + 1) * q).negOnePow • y := by
  have hs : i.negOnePow * (i * (q + 1)).negOnePow = (i * q).negOnePow := by
    rw [mul_add, mul_one, Int.negOnePow_add]
    calc
      i.negOnePow * ((i * q).negOnePow * i.negOnePow) =
          (i * q).negOnePow * (i.negOnePow * i.negOnePow) := by ac_rfl
      _ = (i * q).negOnePow := by rw [Int.units_mul_self, mul_one]
  rw [smul_smul, hs, smul_sub, smul_smul]
  have hc : (i * q).negOnePow * q.negOnePow = ((i + 1) * q).negOnePow := by
    rw [add_mul, one_mul, Int.negOnePow_add]
  rw [hc]
  abel
private theorem generalBidualDegree_comm (E I : RingedSiteComplex.{c, v, r} J R) (i : ℤ) :
    ringedSiteBidualDegree.{c, v, r} J R E I i ≫
        (homComplex.{c, v, max c v r, max c v r} (R := R)
          (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I).d i (i + 1) =
      E.d i (i + 1) ≫ ringedSiteBidualDegree.{c, v, r} J R E I (i + 1) := by
  apply Fan.IsLimit.hom_ext (homComplexIsLimit.{c, v, max c v r, max c v r} (R := R)
    (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I (i + 1))
  intro q
  simp only [fan_mk_proj]
  apply SheafOfModules.hom_ext
  ext U x : 3
  apply PresheafOfModules.hom_ext
  intro W
  ext φ
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have ho := generalHom_d_eval.{c, v, r} J R
    (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I
    i (i + 1) q (q + i) (q + (i + 1)) (q + 1) rfl rfl rfl (by omega)
    U ((ringedSiteBidualDegree.{c, v, r} J R E I i).val.app U x) W φ
  have hl₀ := ringedSiteBidualDegree_eval.{c, v, r} J R E I i q (q + i)
    rfl U x W φ
  have hl₁ := ringedSiteBidualDegree_eval.{c, v, r} J R E I i (q + 1) (q + (i + 1))
    (by omega) U x W
    (((homComplex.{c, v, max c v r, max c v r} (R := R) E I).d q (q + 1)).val.app
      (op W.unop.left) φ)
  have hi := generalHom_d_eval.{c, v, r} J R E I q (q + 1) i
    (q + i) (q + (i + 1)) (i + 1) rfl (by omega) (by omega) (by omega)
    (op W.unop.left) φ (op (Over.mk (𝟙 W.unop.left)))
    ((E.X i).val.map W.unop.hom.op x)
  have hr := ringedSiteBidualDegree_eval.{c, v, r} J R E I (i + 1) q (q + (i + 1))
    rfl U ((E.d i (i + 1)).val.app U x) W φ
  have hx := PresheafOfModules.naturality_apply (E.d i (i + 1)).val W.unop.hom.op x
  rw [← hx] at hr
  rw [hl₀, hl₁, hi] at ho
  apply ho.trans
  apply Eq.trans ?_ hr.symm
  let z : ((PresheafOfModules.restrictOver R.obj U.unop).obj
      (I.X (q + (i + 1))).val).obj W :=
    (I.d (q + i) (q + (i + 1))).val.app (op W.unop.left)
      ((((homComplexπ.{c, v, max c v r, max c v r} (R := R) E I q i (q + i)
        (by omega)).val.app (op W.unop.left) φ).app
          (op (Over.mk (𝟙 W.unop.left)))).hom
            ((E.X i).val.map W.unop.hom.op x))
  let y : ((PresheafOfModules.restrictOver R.obj U.unop).obj
      (I.X (q + (i + 1))).val).obj W :=
    ((((homComplexπ.{c, v, max c v r, max c v r} (R := R) E I q (i + 1)
      (q + (i + 1)) (by omega)).val.app (op W.unop.left) φ).app
        (op (Over.mk (𝟙 W.unop.left)))).hom
          ((E.d i (i + 1)).val.app (op W.unop.left) ((E.X i).val.map W.unop.hom.op x)))
  convert generalBidualSigns i q z y using 1
  simp only [z, y, Units.smul_def, map_zsmul, Over.mk, CostructuredArrow.mk_left]
private def generalOrdinaryBidual (E I : RingedSiteComplex.{c, v, r} J R) :
    E ⟶ homComplex.{c, v, max c v r, max c v r} (R := R)
      (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I where
  f i := ringedSiteBidualDegree.{c, v, r} J R E I i
  comm' i j h := by
    change i + 1 = j at h
    subst j
    exact generalBidualDegree_comm.{c, v, r} J R E I i
private theorem unsignedReindex_proj
    (E I : SignedDoubleHomCone.Complex.{c, v, r, max c v r} R)
    (t p b : ℤ) (h : p + (t + 1) = b) :
    SignedDoubleHomCone.reindexOne.{c, v, r, max c v r} (R := R) E I t ≫
        SignedDoubleHomCone.proj.{c, v, r, max c v r} (R := R)
          (E⟦(1 : ℤ)⟧) I (t + 1) p b h =
      SignedDoubleHomCone.proj.{c, v, r, max c v r} (R := R)
        E I t (p + 1) b (by omega) ≫
        SheafOfModules.homObjMap (R := R)
          (E.shiftFunctorObjXIso 1 p (p + 1) rfl).hom (𝟙 _) := by
  subst b
  exact Fan.IsLimit.fac
    (SignedDoubleHomCone.productLimit.{c, v, r, max c v r} (R := R)
      (E⟦(1 : ℤ)⟧) I (t + 1))
    (fun a : ℤ ↦ SignedDoubleHomCone.proj.{c, v, r, max c v r} (R := R)
      E I t (a + 1) (a + (t + 1)) (by omega) ≫
        SheafOfModules.homObjMap (R := R)
          (E.shiftFunctorObjXIso 1 a (a + 1) rfl).hom (𝟙 _)) p

private theorem unsignedReindex_eval (E I : RingedSiteComplex.{c, v, r} J R)
    (t p b : ℤ) (h : p + (t + 1) = b) (U : Cᵒᵖ)
    (φ : ((homComplex.{c, v, max c v r, max c v r} (R := R) E I).X t).val.obj U)
    (x : ((E⟦(1 : ℤ)⟧).X p).val.obj U) :
    (((homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦(1 : ℤ)⟧) I
      (t + 1) p b h).val.app U
        ((SignedDoubleHomCone.reindexOne.{c, v, max c v r, max c v r} E I t).val.app U φ)).app
          (op (Over.mk (𝟙 U.unop)))).hom x =
    (((homComplexπ.{c, v, max c v r, max c v r} (R := R) E I t (p + 1) b
      (by omega)).val.app U φ).app (op (Over.mk (𝟙 U.unop)))).hom x := by
  have hp := unsignedReindex_proj.{c, v, r} J R E I t p b h
  simp only [SignedDoubleHomCone.proj, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, SheafOfModules.homObjMap_id, Category.comp_id] at hp
  exact congrArg (fun f ↦ ((f.val.app U φ).app (op (Over.mk (𝟙 U.unop)))).hom x) hp
private theorem bidualShiftSigns {G : Type*} [AddCommGroup G] (p t : ℤ) (y : G) :
    (p + t).negOnePow • ((p * (t + 1)).negOnePow • y) =
      ((p + 1) * t).negOnePow • y := by
  rw [smul_smul]
  congr 1
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
  exact ⟨p, by ring⟩
private theorem ordinaryBidual_shift_with
    (E I : RingedSiteComplex.{c, v, r} J R)
    (χ : homComplex.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) (E⟦(1 : ℤ)⟧) I) I ≅
      (homComplex.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I)⟦(1 : ℤ)⟧)
    (hχ : ∀ p t : ℤ,
      χ.hom.f p ≫ homComplexπ.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I
        (p + 1) t (t + (p + 1)) rfl =
      (p + t).negOnePow •
        (homComplexπ.{c, v, max c v r, max c v r} (R := R)
          (homComplex.{c, v, max c v r, max c v r} (R := R) (E⟦(1 : ℤ)⟧) I) I
          p (t + 1) (t + (p + 1)) (by omega) ≫
            SheafOfModules.homObjMap (R := R)
              (SignedDoubleHomCone.reindexOne.{c, v, max c v r, max c v r} E I t) (𝟙 _))) :
    generalOrdinaryBidual.{c, v, r} J R (E⟦(1 : ℤ)⟧) I ≫ χ.hom =
      (generalOrdinaryBidual.{c, v, r} J R E I)⟦(1 : ℤ)⟧' := by
  apply HomologicalComplex.hom_ext
  intro p
  apply Fan.IsLimit.hom_ext (homComplexIsLimit.{c, v, max c v r, max c v r} (R := R)
    (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I (p + 1))
  intro t
  change (ringedSiteBidualDegree.{c, v, r} J R (E⟦(1 : ℤ)⟧) I p ≫ χ.hom.f p) ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I
        (p + 1) t (t + (p + 1)) rfl =
    ringedSiteBidualDegree.{c, v, r} J R E I (p + 1) ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I
        (p + 1) t (t + (p + 1)) rfl
  rw [Category.assoc, hχ, Linear.comp_units_smul]
  apply SheafOfModules.hom_ext
  ext U x : 3
  apply PresheafOfModules.hom_ext
  intro W
  ext φ
  let ev : ((E⟦(1 : ℤ)⟧).X p ⟶ SheafOfModules.homObj (R := R)
      ((homComplex.{c, v, max c v r, max c v r} (R := R) E I).X t)
      (I.X (t + (p + 1)))) →+
        ((PresheafOfModules.restrictOver R.obj U.unop).obj
          (I.X (t + (p + 1))).val).obj W :=
    { toFun f := ((f.val.app U x).app W).hom φ
      map_zero' := rfl
      map_add' _ _ := rfl }
  change ev ((p + t).negOnePow • _) = ev _
  simp only [Units.smul_def, map_zsmul]
  have hb := ringedSiteBidualDegree_eval.{c, v, r} J R (E⟦(1 : ℤ)⟧) I p (t + 1)
    (t + (p + 1)) (by omega) U x W
    ((SignedDoubleHomCone.reindexOne.{c, v, max c v r, max c v r} E I t).val.app
      (op W.unop.left) φ)
  have hr := ringedSiteBidualDegree_eval.{c, v, r} J R E I (p + 1) t
    (t + (p + 1)) rfl U x W φ
  erw [hb, hr]
  have hu := unsignedReindex_eval.{c, v, r} J R E I t p (t + (p + 1)) (by omega)
    (op W.unop.left) φ (((E⟦(1 : ℤ)⟧).X p).val.map W.unop.hom.op x)
  rw [hu]
  let z : ((PresheafOfModules.restrictOver R.obj U.unop).obj
      (I.X (t + (p + 1))).val).obj W :=
    ((((homComplexπ.{c, v, max c v r, max c v r} (R := R) E I t (p + 1)
      (t + (p + 1)) (by omega)).val.app (op W.unop.left) φ).app
        (op (Over.mk (𝟙 W.unop.left)))).hom ((E.X (p + 1)).val.map W.unop.hom.op x))
  convert bidualShiftSigns p t z using 1
  simp only [z, Units.smul_def, CochainComplex.shiftFunctor_obj_X']
private theorem ordinaryBidual_naturality
    {E F : RingedSiteComplex.{c, v, r} J R} (I : RingedSiteComplex.{c, v, r} J R)
    (f : E ⟶ F) :
    f ≫ generalOrdinaryBidual.{c, v, r} J R F I =
      generalOrdinaryBidual.{c, v, r} J R E I ≫
        (SignedDoubleHomCone.doubleDual.{c, v, max c v r, max c v r} I).map f := by
  apply HomologicalComplex.hom_ext
  intro i
  apply Fan.IsLimit.hom_ext (homComplexIsLimit.{c, v, max c v r, max c v r} (R := R)
    (homComplex.{c, v, max c v r, max c v r} (R := R) F I) I i)
  intro q
  change (f.f i ≫ ringedSiteBidualDegree.{c, v, r} J R F I i) ≫
      homComplexπ.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) F I) I i q (q + i) rfl = _
  let d := ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map f.op).app I
  have ho := homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} (R := R)
    d (𝟙 I) i q (q + i) rfl
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at ho
  change _ = (ringedSiteBidualDegree.{c, v, r} J R E I i ≫
    (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map d.op).app I).f i) ≫ _
  simp only [Category.assoc]
  erw [ho]
  apply SheafOfModules.hom_ext
  ext U x : 3
  apply PresheafOfModules.hom_ext
  intro W
  ext φ
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have hl := ringedSiteBidualDegree_eval.{c, v, r} J R F I i q (q + i)
    rfl U ((f.f i).val.app U x) W φ
  have hr := ringedSiteBidualDegree_eval.{c, v, r} J R E I i q (q + i)
    rfl U x W ((d.f q).val.app (op W.unop.left) φ)
  have hi := homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} (R := R)
    f (𝟙 I) q i (q + i) (by omega)
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at hi
  have he := congrArg (fun k ↦
    ((k.val.app (op W.unop.left) φ).app (op (Over.mk (𝟙 W.unop.left)))).hom
      ((E.X i).val.map W.unop.hom.op x)) hi
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at he
  have hx := PresheafOfModules.naturality_apply (f.f i).val W.unop.hom.op x
  rw [← hx] at hl
  erw [hl, hr]
  exact congrArg (fun z ↦ (i * q).negOnePow • z) he.symm

end CategoryTheory

namespace CategoryTheory.RingedHomUniverses

set_option backward.isDefEq.respectTransparency true in
private theorem resolvedSourceShiftDescent
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ]
    (W : MorphismProperty A) [W.ContainsIdentities] [Q.IsLocalization W]
    (U : Aᵒᵖ × A ⥤ A) (I : A ⥤ A) (η : 𝟭 A ⟶ I)
    (H : Bᵒᵖ × B ⥤ B)
    (fac : (Q.op.prod Q) ⋙ H ≅ (𝟭 _).prod I ⋙ U ⋙ Q)
    (s : ℤ)
    (e : U ⋙ shiftFunctor A (-s) ≅
      ((shiftFunctor A s).op.prod (𝟭 A)) ⋙ U) :
    let α : U ⋙ Q ⟶ (Q.op.prod Q) ⋙ H :=
      Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 Aᵒᵖ)) η) (U ⋙ Q) ≫ fac.inv
    ∃ t : H ⋙ shiftFunctor B (-s) ≅
      ((shiftFunctor B s).op.prod (𝟭 B)) ⋙ H,
      (∀ (L M : A),
        t.hom.app (op (Q.obj L), Q.obj M) =
          (fac.hom.app (op L, M))⟦-s⟧' ≫
            (Q.commShiftIso (-s)).inv.app (U.obj (op L, I.obj M)) ≫
            Q.map ((e.app (op L, I.obj M)).hom) ≫
            fac.inv.app (op (L⟦s⟧), M) ≫
            H.map (Prod.mkHom (((Q.commShiftIso s).inv.app L).op) (𝟙 _))) ∧
      ∀ (L M : A),
        (Q.commShiftIso (-s)).hom.app (U.obj (op L, M)) ≫
            (α.app (op L, M))⟦-s⟧' ≫ t.hom.app (op (Q.obj L), Q.obj M) =
          Q.map ((e.app (op L, M)).hom) ≫ α.app (op (L⟦s⟧), M) ≫
            H.map (Prod.mkHom (((Q.commShiftIso s).inv.app L).op) (𝟙 _)) := by
  classical
  intro α
  let P := Q.op.prod Q
  let V := W.op.prod W
  let S := (shiftFunctor A s).op.prod (𝟭 A)
  let q : S ⋙ P ≅ P ⋙ ((shiftFunctor B s).op.prod (𝟭 B)) :=
    NatIso.prod (NatIso.op (Q.commShiftIso s).symm) (Iso.refl Q)
  let f : P ⋙ (H ⋙ shiftFunctor B (-s)) ≅
      P ⋙ (((shiftFunctor B s).op.prod (𝟭 B)) ⋙ H) :=
    Functor.isoWhiskerRight fac (shiftFunctor B (-s)) ≪≫
      Functor.isoWhiskerLeft ((𝟭 _).prod I ⋙ U) (Q.commShiftIso (-s)).symm ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft ((𝟭 _).prod I) e) Q ≪≫
      (Functor.isoWhiskerLeft S fac).symm ≪≫ Functor.isoWhiskerRight q H
  let ff := Localization.fullyFaithfulWhiskeringLeft P V B
  let t := ff.preimageIso f
  have ht (L M : A) :
      t.hom.app (P.obj (op L, M)) = f.hom.app (op L, M) :=
    NatTrans.congr_app (ff.map_preimage f.hom) (op L, M)
  refine ⟨t, ?_, ?_⟩
  · intro L M
    simpa [f, q, S, P, NatTrans.prod] using ht L M
  intro L M
  have ht : t.hom.app (P.obj (op L, M)) = f.hom.app (op L, M) :=
    NatTrans.congr_app (ff.map_preimage f.hom) (op L, M)
  dsimp only [P, Functor.prod_obj, Functor.op_obj] at ht
  rw [ht]
  dsimp only [f, α, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp]
  dsimp only [Functor.comp_map, Functor.comp_obj, NatTrans.prod, NatTrans.id_app,
    Functor.id_obj, Functor.prod_obj, Functor.whiskerLeft_app]
  rw [← Functor.commShiftIso_hom_naturality_assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc]
  have hn := e.hom.naturality (Prod.mkHom (𝟙 (op L)) (η.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_obj,
    Functor.prod_map, Functor.op_map, Functor.id_map, Functor.map_id,
    Functor.op_obj, Functor.id_obj] at hn
  rw [hn]
  simp only [unop_id, Functor.map_id, op_id, Functor.map_comp, Category.assoc]
  rfl


set_option backward.isDefEq.respectTransparency true in
private theorem resolvedNormalizedSourceShiftDescent
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ]
    (W : MorphismProperty A) [W.ContainsIdentities] [Q.IsLocalization W]
    (U : Aᵒᵖ × A ⥤ A) (I : A ⥤ A) (η : 𝟭 A ⟶ I)
    (H : Bᵒᵖ × B ⥤ B)
    (fac : (Q.op.prod Q) ⋙ H ≅ (𝟭 _).prod I ⋙ U ⋙ Q)
    (s : ℤ)
    (e : U ⋙ shiftFunctor A (-s) ≅
      ((shiftFunctor A s).op.prod (𝟭 A)) ⋙ U) :
    let α : U ⋙ Q ⟶ (Q.op.prod Q) ⋙ H :=
      Functor.whiskerRight (NatTrans.prod (𝟙 (𝟭 Aᵒᵖ)) η) (U ⋙ Q) ≫ fac.inv
    ∃ S : ∀ P : B,
      (Functor.curry.obj H).obj (op P) ⋙ shiftFunctor B (-s) ≅
        (Functor.curry.obj H).obj (op (P⟦s⟧)),
      (∀ (P : B) (L F : A) (eP : Q.obj L ≅ P),
        (Q.commShiftIso (-s)).hom.app (U.obj (op L, F)) ≫
            (α.app (op L, F) ≫ H.map (Prod.mkHom eP.inv.op (𝟙 _)))⟦-s⟧' ≫
              (S P).hom.app (Q.obj F) =
          Q.map ((e.app (op L, F)).hom) ≫ α.app (op (L⟦s⟧), F) ≫
            H.map (Prod.mkHom (((shiftFunctor B s).map eP.inv) ≫
              (Q.commShiftIso s).inv.app L).op (𝟙 _))) ∧
      (∀ (P : B) (L F : A) (eP : Q.obj L ≅ P),
        (Q.commShiftIso (-s)).hom.app (U.obj (op L, I.obj F)) ≫
            (fac.inv.app (op L, F) ≫
              H.map (Prod.mkHom eP.inv.op (𝟙 _)))⟦-s⟧' ≫
              (S P).hom.app (Q.obj F) =
          Q.map ((e.app (op L, I.obj F)).hom) ≫ fac.inv.app (op (L⟦s⟧), F) ≫
            H.map (Prod.mkHom (((shiftFunctor B s).map eP.inv) ≫
              (Q.commShiftIso s).inv.app L).op (𝟙 _))) ∧
      ∀ (P P' N : B) (f : P' ⟶ P),
        (H.map (Prod.mkHom f.op (𝟙 N)))⟦-s⟧' ≫ (S P').hom.app N =
          (S P).hom.app N ≫
            H.map (Prod.mkHom (f⟦s⟧').op (𝟙 N)) := by
  intro α
  obtain ⟨t, hr, ht⟩ := resolvedSourceShiftDescent Q W U I η H fac s e
  let S (P : B) : (Functor.curry.obj H).obj (op P) ⋙ shiftFunctor B (-s) ≅
      (Functor.curry.obj H).obj (op (P⟦s⟧)) :=
    NatIso.ofComponents (fun N ↦ t.app (op P, N)) (by
      intro N N' f
      simpa only [Functor.comp_map, Functor.curry_obj_obj_map, Iso.app_hom,
        Functor.prod_map, Functor.op_map, unop_id, Functor.map_id, op_id,
        Functor.id_map] using t.hom.naturality (Prod.mkHom (𝟙 (op P)) f))
  have hn (P : B) (L F : A) (eP : Q.obj L ≅ P) :=
    t.hom.naturality (Prod.mkHom eP.inv.op (𝟙 (Q.obj F)))
  refine ⟨S, ?_, ?_⟩
  swap
  · constructor
    · intro P L F eP
      have hn := hn P L F eP
      change (H.map (Prod.mkHom eP.inv.op (𝟙 (Q.obj F))))⟦-s⟧' ≫
        t.hom.app (op P, Q.obj F) =
          t.hom.app (op (Q.obj L), Q.obj F) ≫
            H.map (Prod.mkHom ((shiftFunctor B s).map eP.inv).op (𝟙 _)) at hn
      change _ ≫ _ ≫ t.hom.app (op P, Q.obj F) = _
      simp only [Functor.map_comp, Category.assoc]
      rw [hn, hr L F]
      simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        Category.id_comp, ← H.map_comp, prod_comp, ← op_comp]
      simp [Functor.comp_obj]
    · intro P P' N f
      exact t.hom.naturality (Prod.mkHom f.op (𝟙 N))
  intro P L F eP
  have hn := t.hom.naturality (Prod.mkHom eP.inv.op (𝟙 (Q.obj F)))
  change (H.map (Prod.mkHom eP.inv.op (𝟙 (Q.obj F))))⟦-s⟧' ≫
      t.hom.app (op P, Q.obj F) =
    t.hom.app (op (Q.obj L), Q.obj F) ≫
      H.map (Prod.mkHom ((shiftFunctor B s).map eP.inv).op (𝟙 (Q.obj F))) at hn
  change _ ≫ _ ≫ t.hom.app (op P, Q.obj F) = _
  calc
    _ = ((Q.commShiftIso (-s)).hom.app (U.obj (op L, F)) ≫
        (α.app (op L, F))⟦-s⟧' ≫ t.hom.app (op (Q.obj L), Q.obj F)) ≫
          H.map (Prod.mkHom ((shiftFunctor B s).map eP.inv).op (𝟙 (Q.obj F))) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hn]
    _ = (Q.map ((e.app (op L, F)).hom) ≫ α.app (op (L⟦s⟧), F) ≫
        H.map (Prod.mkHom (((Q.commShiftIso s).inv.app L).op) (𝟙 _))) ≫
          H.map (Prod.mkHom ((shiftFunctor B s).map eP.inv).op (𝟙 (Q.obj F))) := by
      rw [ht L F]
    _ = _ := by
      simp only [Category.assoc, ← H.map_comp, prod_comp,
        Category.id_comp, ← op_comp]


private def doubleComparison
    {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) (U : Aᵒᵖ ⥤ A) (T : Bᵒᵖ ⥤ B)
    (α : U ⋙ Q ≅ Q.op ⋙ T) (E : A) :
    Q.obj ((U.rightOp ⋙ U).obj E) ≅ (T.rightOp ⋙ T).obj (Q.obj E) :=
  α.app (op (U.obj (op E))) ≪≫ T.mapIso (α.app (op E)).symm.op

private theorem doubleComparison_naturality
    {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) (U : Aᵒᵖ ⥤ A) (T : Bᵒᵖ ⥤ B)
    (α : U ⋙ Q ≅ Q.op ⋙ T) {E F : A} (f : E ⟶ F) :
    Q.map ((U.rightOp ⋙ U).map f) ≫ (doubleComparison Q U T α F).hom =
      (doubleComparison Q U T α E).hom ≫ (T.rightOp ⋙ T).map (Q.map f) := by
  let δ : (U.rightOp ⋙ U) ⋙ Q ⟶ Q ⋙ (T.rightOp ⋙ T) :=
    Functor.whiskerLeft U.rightOp α.hom ≫ Functor.whiskerRight α.inv.rightOp T
  exact δ.naturality f

set_option backward.isDefEq.respectTransparency true in
private theorem doubleComparison_source
    {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) (U : Aᵒᵖ ⥤ A) (T : Bᵒᵖ ⥤ B)
    (α : U ⋙ Q ≅ Q.op ⋙ T) (E L : A)
    (a : L ⟶ U.obj (op E)) (b : E ⟶ (U.rightOp ⋙ U).obj E) :
    Q.map b ≫ (doubleComparison Q U T α E).hom ≫
        T.map (Q.map a ≫ (α.app (op E)).hom).op =
      Q.map (b ≫ U.map a.op) ≫ (α.app (op L)).hom := by
  have hn := α.hom.naturality a.op
  change Q.map (U.map a.op) ≫ (α.app (op L)).hom =
    (α.app (op (U.obj (op E)))).hom ≫ T.map (Q.map a).op at hn
  simp only [doubleComparison, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, Iso.symm_hom, op_comp, Functor.map_comp, Category.assoc]
  erw [← T.map_comp_assoc, ← op_comp, Iso.hom_inv_id, op_id, T.map_id,
    Category.id_comp, ← hn]

set_option backward.isDefEq.respectTransparency true in
private theorem doubleShift_compare
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasShift A ℤ] [HasShift B ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] [Q.Additive]
    (U : Aᵒᵖ ⥤ A) (T : Bᵒᵖ ⥤ B)
    (α : U ⋙ Q ≅ Q.op ⋙ T)
    (s : ∀ (L : A) (m : ℤ), U.obj (op (L⟦m⟧)) ≅ (U.obj (op L))⟦-m⟧)
    (κ : ∀ (P : B) (m : ℤ), (T.obj (op P))⟦-m⟧ ≅ T.obj (op (P⟦m⟧)))
    (hκ : ∀ (P : B) (L : A) (eP : Q.obj L ≅ P) (m : ℤ),
      (Q.commShiftIso (-m)).hom.app (U.obj (op L)) ≫
          ((α.app (op L)).hom ≫ T.map eP.inv.op)⟦-m⟧' ≫ (κ P m).hom =
        Q.map (s L m).inv ≫ (α.app (op (L⟦m⟧))).hom ≫
          T.map (((eP.inv)⟦m⟧' ≫ (Q.commShiftIso m).inv.app L).op))
    (E : A) :
    Q.map (-(U.map (s E 1).inv.op ≫ (s (U.obj (op E)) (-1)).hom)) ≫
        (Q.commShiftIso 1).hom.app ((U.rightOp ⋙ U).obj E) ≫
        ((doubleComparison Q U T α E).hom)⟦(1 : ℤ)⟧' =
      (doubleComparison Q U T α (E⟦(1 : ℤ)⟧)).hom ≫
        (T.rightOp ⋙ T).map ((Q.commShiftIso 1).hom.app E) ≫
        (-(T.map (κ (Q.obj E) 1).hom.op ≫ (κ (T.obj (op (Q.obj E))) (-1)).inv)) := by
  have hi := hκ (Q.obj E) E (Iso.refl _) 1
  simp only [Iso.refl_inv, op_id] at hi
  simp only [Functor.map_id, Category.id_comp] at hi
  erw [T.map_id, Category.comp_id] at hi
  have ho := hκ (T.obj (op (Q.obj E))) (U.obj (op E)) (α.app (op E)) (-1)
  change (Q.commShiftIso 1).hom.app (U.obj (op (U.obj (op E)))) ≫
      ((α.app (op (U.obj (op E)))).hom ≫ T.map (α.app (op E)).inv.op)⟦(1 : ℤ)⟧' ≫
      (κ (T.obj (op (Q.obj E))) (-1)).hom =
    Q.map (s (U.obj (op E)) (-1)).inv ≫
      (α.app (op ((U.obj (op E))⟦(-1 : ℤ)⟧))).hom ≫
      T.map (((α.app (op E)).inv)⟦(-1 : ℤ)⟧' ≫
        (Q.commShiftIso (-1)).inv.app (U.obj (op E))).op at ho
  have hn := α.hom.naturality (s E 1).inv.op
  change Q.map (U.map (s E 1).inv.op) ≫ (α.app (op ((U.obj (op E))⟦(-1 : ℤ)⟧))).hom =
    (α.app (op (U.obj (op (E⟦(1 : ℤ)⟧))))).hom ≫
      T.map (Q.map (s E 1).inv).op at hn
  have hu :
      ((α.app (op E)).inv)⟦(-1 : ℤ)⟧' ≫
          (Q.commShiftIso (-1)).inv.app (U.obj (op E)) ≫ Q.map (s E 1).inv =
        (κ (Q.obj E) 1).hom ≫ T.map ((Q.commShiftIso 1).hom.app E).op ≫
          (α.app (op (E⟦(1 : ℤ)⟧))).inv := by
    apply (cancel_epi ((Q.commShiftIso (-1)).hom.app (U.obj (op E)) ≫
      ((α.app (op E)).hom)⟦(-1 : ℤ)⟧')).mp
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id]
    simp only [Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
    have hc := congrArg (fun f ↦ f ≫ T.map ((Q.commShiftIso 1).hom.app E).op ≫
      (α.app (op (E⟦(1 : ℤ)⟧))).inv) hi.symm
    simp only [Category.assoc, ← T.map_comp_assoc, ← op_comp,
      Iso.hom_inv_id_app, op_id] at hc
    erw [T.map_id, Category.id_comp, Iso.hom_inv_id, Category.comp_id] at hc
    exact hc
  simp only [Functor.map_neg, Functor.map_comp, Preadditive.neg_comp,
    Preadditive.comp_neg, Category.assoc]
  apply congrArg Neg.neg
  apply (cancel_mono (κ (T.obj (op (Q.obj E))) (-1)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change Q.map (U.map (s E 1).inv.op) ≫ Q.map (s (U.obj (op E)) (-1)).hom ≫
      (Q.commShiftIso 1).hom.app _ ≫ (doubleComparison Q U T α E).hom⟦(1 : ℤ)⟧' ≫
        (κ (T.obj (op (Q.obj E))) (-1)).hom = _
  erw [show (doubleComparison Q U T α E).hom =
    (α.app (op (U.obj (op E)))).hom ≫ T.map (α.app (op E)).inv.op from rfl]
  erw [ho]
  simp only [← Q.map_comp_assoc, Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  erw [← Category.assoc, hn]
  simp only [doubleComparison, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    Iso.symm_hom, Iso.app_hom, Category.assoc,
    Functor.comp_map, Functor.rightOp_map]
  erw [← T.map_comp, ← op_comp]
  simp only [Category.assoc]
  erw [hu]
  simp only [op_comp, Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency true in
private def doubleShiftNatTrans
    {B : Type*} [Category B] [Preadditive B] [HasShift B ℤ]
    (T : Bᵒᵖ ⥤ B)
    (κ : ∀ (P : B) (m : ℤ), (T.obj (op P))⟦-m⟧ ≅ T.obj (op (P⟦m⟧)))
    (hκ : ∀ (P P' : B) (f : P' ⟶ P) (m : ℤ),
      (T.map f.op)⟦-m⟧' ≫ (κ P' m).hom =
        (κ P m).hom ≫ T.map (f⟦m⟧').op) :
    shiftFunctor B (1 : ℤ) ⋙ (T.rightOp ⋙ T) ⟶
      (T.rightOp ⋙ T) ⋙ shiftFunctor B (1 : ℤ) where
  app X := -(T.map (κ X 1).hom.op ≫ (κ (T.obj (op X)) (-1)).inv)
  naturality X Y f := by
    have hi := hκ Y X f 1
    have ho := hκ (T.obj (op X)) (T.obj (op Y)) (T.map f.op) (-1)
    dsimp only [Functor.comp_map, Functor.rightOp_map]
    simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc]
    apply congrArg Neg.neg
    rw [← T.map_comp_assoc, ← op_comp, ← hi, op_comp, Functor.map_comp]
    simp only [Category.assoc]
    congr 1
    apply (cancel_mono (κ (T.obj (op Y)) (-1)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [ho, Iso.inv_hom_id_assoc]

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

private abbrev resolvedTarget (B : Complex.{c, v, r} J R) :=
  (WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj B

private abbrev resolvedDual (K : D.{c, v, r, w} J R) :=
  Prod.sectL _ K ⋙ derivedInternalHomOfUniverses.{c, v, r, w} J R

set_option backward.isDefEq.respectTransparency true in
private theorem sourceShift_resolved
    (e : ∀ s : ℤ, ordinaryBifunctor.{c, v, r} J R ⋙ shiftFunctor _ (-s) ≅
      ((shiftFunctor (Complex.{c, v, r} J R) s).op.prod (𝟭 _)) ⋙
        ordinaryBifunctor.{c, v, r} J R)
    (he : ∀ (s : ℤ) (L F : Complex.{c, v, r} J R),
      LeftFormula.{c, v, r} J R L F s ((e s).app (op L, F)))
    (P : D.{c, v, r, w} J R) (L F : Complex.{c, v, r} J R)
    (eP : DerivedCategory.Q.obj L ≅ P) (s : ℤ) :
    (DerivedCategory.Q.commShiftIso (-s)).hom.app
        (complexHom.{c, v, r} J R L
          ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj F)) ≫
      ((WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L F).inv ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom eP.inv.op (𝟙 _)))⟦-s⟧' ≫
      (sourceShift.{c, v, r, w} J R P s).hom.app (DerivedCategory.Q.obj F) =
    DerivedCategory.Q.map ((e s).app
      (op L, (WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj F)).hom ≫
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R (L⟦s⟧) F).inv ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (((shiftFunctor _ s).map eP.inv) ≫
          (DerivedCategory.Q.commShiftIso s).inv.app L).op (𝟙 _)) := by
  classical
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let U := ordinaryBifunctor.{c, v, r} J R
  let I := WeilConjectures.coefficientHomResolution.{r, c, v} J R
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  have hd (m : ℤ) := resolvedNormalizedSourceShiftDescent Q
    (HomologicalComplex.quasiIso (Modules.{c, v, r} J R) (.up ℤ))
    U I (ringedSiteHomAugmentation.{c, v, r} J R) H
    (resolutionComparison.{c, v, r, w} J R) m (e m)
  choose S hS hr hn using hd
  have hN : LeftNormalization.{c, v, r, w} J R (fun P m ↦ S m P) := by
    intro P L F eP m
    exact ⟨(e m).app (op L, F), he m L F, hS m P L F eP⟩
  have hEq : (fun P m ↦ S m P) =
      (leftShift_existsUnique.{c, v, r, w} J R).exists.choose :=
    (leftShift_existsUnique.{c, v, r, w} J R).unique hN
      (leftShift_existsUnique.{c, v, r, w} J R).exists.choose_spec
  change _ ≫ _ ≫
    ((leftShift_existsUnique.{c, v, r, w} J R).exists.choose P s).hom.app _ = _
  rw [← hEq]
  exact hr s P L F eP

omit [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] in
set_option backward.isDefEq.respectTransparency true in
private theorem signedHomShift_inv_formula
    (I L : Complex.{c, v, r} J R) (s : ℤ)
    (σ : homComplex.{c, v, max c v r, max c v r} (R := R) (L⟦s⟧) I ≅
      (homComplex.{c, v, max c v r, max c v r} (R := R) L I)⟦-s⟧)
    (hσ : ∀ k p : ℤ,
      σ.hom.f k ≫
          ((homComplex.{c, v, max c v r, max c v r} (R := R) L I).shiftFunctorObjXIso
            (-s) k (k - s) (by omega)).hom ≫
          SignedDoubleHomCone.proj.{c, v, r, max c v r} (R := R)
            L I (k - s) (p + s) (p + k) (by omega) =
        (s * k).negOnePow •
          (SignedDoubleHomCone.proj.{c, v, r, max c v r} (R := R)
            (L⟦s⟧) I k p (p + k) rfl ≫
          SheafOfModules.homObjMap (R := R) (L.shiftFunctorObjXIso s p (p + s) rfl).inv (𝟙 _))) :
    LeftFormula.{c, v, r} J R L I s σ.symm := by
  intro k p q h
  subst q
  have hp := hσ k p
  simp only [SignedDoubleHomCone.proj, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv] at hp
  dsimp only [CochainComplex.shiftFunctor_obj_X'] at hp ⊢
  simp only [Category.id_comp, SheafOfModules.homObjMap_id, Category.comp_id] at hp
  change σ.inv.f k ≫ _ = _
  apply (cancel_epi (σ.hom.f k)).mp
  erw [← Category.assoc, ← HomologicalComplex.comp_f, σ.hom_inv_id,
    HomologicalComplex.id_f, Category.id_comp, Linear.comp_units_smul]
  change _ = (s * k).negOnePow • (_ ≫ _)
  erw [show σ.hom.f k ≫ _ = _ from hp, smul_smul,
    Int.units_mul_self, one_smul]

set_option backward.isDefEq.respectTransparency true in
private theorem sourceShift_signed
    (P : D.{c, v, r, w} J R) (L F : Complex.{c, v, r} J R)
    (eP : DerivedCategory.Q.obj L ≅ P) (s : ℤ)
    (σ : (complexHom.{c, v, r} J R L (resolvedTarget.{c, v, r} J R F))⟦-s⟧ ≅
      complexHom.{c, v, r} J R (L⟦s⟧) (resolvedTarget.{c, v, r} J R F))
    (hσ : LeftFormula.{c, v, r} J R L (resolvedTarget.{c, v, r} J R F) s σ) :
    (DerivedCategory.Q.commShiftIso (-s)).hom.app
        (complexHom.{c, v, r} J R L
          ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj F)) ≫
      ((WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L F).inv ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom eP.inv.op (𝟙 _)))⟦-s⟧' ≫
      (sourceShift.{c, v, r, w} J R P s).hom.app (DerivedCategory.Q.obj F) =
    DerivedCategory.Q.map
      σ.hom ≫
      (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R (L⟦s⟧) F).inv ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom (((shiftFunctor _ s).map eP.inv) ≫
          (DerivedCategory.Q.commShiftIso s).inv.app L).op (𝟙 _)) := by
  classical
  choose e he using ordinaryLeftShift.{c, v, r} J R
  have h := sourceShift_resolved.{c, v, r, w} J R e he P L F eP s
  have hEq := leftFormula_unique.{c, v, r} J R L
    ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj F) s
    ((e s).app (op L, (WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj F))
    σ (he s L _) hσ
  rw [hEq] at h
  exact h


set_option backward.isDefEq.respectTransparency true in
private theorem sourceShift_naturality
    (P P' N : D.{c, v, r, w} J R) (f : P' ⟶ P) (s : ℤ) :
    ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map
      (Prod.mkHom f.op (𝟙 N)))⟦-s⟧' ≫ (sourceShift.{c, v, r, w} J R P' s).hom.app N =
      (sourceShift.{c, v, r, w} J R P s).hom.app N ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
          (Prod.mkHom (f⟦s⟧').op (𝟙 N)) := by
  classical
  choose e he using ordinaryLeftShift.{c, v, r} J R
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let U := ordinaryBifunctor.{c, v, r} J R
  let I := WeilConjectures.coefficientHomResolution.{r, c, v} J R
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
  have hd (m : ℤ) := resolvedNormalizedSourceShiftDescent Q
    (HomologicalComplex.quasiIso (Modules.{c, v, r} J R) (.up ℤ))
    U I (ringedSiteHomAugmentation.{c, v, r} J R) H
    (resolutionComparison.{c, v, r, w} J R) m (e m)
  choose S hS hr hn using hd
  have hN : LeftNormalization.{c, v, r, w} J R (fun P m ↦ S m P) := by
    intro P L F eP m
    exact ⟨(e m).app (op L, F), he m L F, hS m P L F eP⟩
  have hEq : (fun P m ↦ S m P) =
      (leftShift_existsUnique.{c, v, r, w} J R).exists.choose :=
    (leftShift_existsUnique.{c, v, r, w} J R).unique hN
      (leftShift_existsUnique.{c, v, r, w} J R).exists.choose_spec
  change _ ≫ ((leftShift_existsUnique.{c, v, r, w} J R).exists.choose P' s).hom.app N =
    ((leftShift_existsUnique.{c, v, r, w} J R).exists.choose P s).hom.app N ≫ _
  rw [← hEq]
  exact hn s P P' N f

set_option backward.isDefEq.respectTransparency false in
private def dualResolutionIso (B : Complex.{c, v, r} J R) :
    SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := R)
        (resolvedTarget.{c, v, r} J R B) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q.op ⋙
        resolvedDual.{c, v, r, w} J R (DerivedCategory.Q.obj B) :=
  NatIso.ofComponents
    (fun L ↦ (WeilConjectures.coefficientHomResolutionIso.{r, c, v, w} J R L.unop B).symm)
    (by
      intro L L' f
      have h := (resolutionComparison.{c, v, r, w} J R).inv.naturality
        (Prod.mkHom f (𝟙 B))
      dsimp only [resolutionComparison, Functor.comp_map, Functor.prod_map,
        Functor.prod_obj, Functor.id_map, Functor.id_obj, Functor.uncurry_obj_map,
        Functor.op_map, NatIso.ofComponents_inv_app] at h
      simpa only [SignedDoubleHomCone.dual, resolvedDual,
        Functor.comp_map, Functor.flip_obj_map, Functor.op_map, Prod.sectL_map,
        Iso.symm_hom, Functor.map_id, Category.comp_id] using h)

end CategoryTheory.RingedHomUniverses

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

private theorem comparison_uncurry_square {A : Type*} [Category A]
    {P P' E E' I O : A} (e : P ≅ E) (e' : P' ≅ E')
    (s : E ⟶ E') (σ : P ⟶ P') (ψ : P' ⟶ I) (φ : P ⟶ I)
    (η : I ⟶ O) (u : E ⟶ O) (u' : E' ⟶ O)
    (hσ : e.hom ≫ s = σ ≫ e'.hom)
    (hφ : e.hom ≫ u = φ ≫ η) (hψ : e'.hom ≫ u' = ψ ≫ η)
    (h : φ = σ ≫ ψ) : u = s ≫ u' := by
  apply (cancel_epi e.hom).mp
  calc
    e.hom ≫ u = φ ≫ η := hφ
    _ = σ ≫ (ψ ≫ η) := by rw [h, Category.assoc]
    _ = σ ≫ (e'.hom ≫ u') := by rw [hψ]
    _ = e.hom ≫ s ≫ u' := by rw [← Category.assoc, ← hσ, Category.assoc]

private theorem bidual_uncurry_square
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (S : WeilConjectures.CoefficientClosedStructure H)
    (s : @SymmetricCategory A _ S.monoidal)
    (E L O : A) (a : L ⟶ H.obj (op E, O)) :
    (S.transpose E L O).symm
        (ringedSiteBidual S s O E ≫ H.map (Prod.mkHom a.op (𝟙 O))) =
      (s.braiding E L).hom ≫ (S.transpose L E O).symm a := by
  let := S.monoidal
  let := s
  unfold ringedSiteBidual
  rw [← ringedSiteTranspose_source, Equiv.symm_apply_apply]
  dsimp only [WeilConjectures.CoefficientClosedStructure.tensor]
  simp only [tensor_map, id_tensorHom]
  erw [BraidedCategory.braiding_naturality_right_assoc]
  rfl

set_option backward.isDefEq.respectTransparency true in
omit [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] in
private theorem totalTensor_generator_ext
    (P L N : Complex.{c, v, r} J R)
    (a b : (WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, L) ⟶ N)
    (h : ∀ (p q k : ℤ) (hpq : p + q = k) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (L.X q).val.obj U),
      (a.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P L p q k hpq U x y) =
        (b.f k).val.app U
          (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R P L p q k hpq U x y)) :
    a = b := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (P.X p) (L.X q)).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 _)).homEquiv
    ((P.X p).val ⊗ (L.X q).val) (N.X k)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h p q k hpq U x y

set_option backward.isDefEq.respectTransparency true in
omit [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] in
private theorem bidual_precompose_formula
    (E L B : Complex.{c, v, r} J R)
    (a : L ⟶ homComplex.{c, v, max c v r, max c v r} (R := R) E
      ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj B))
    (p q k : ℤ) (hpq : p + q = k) (hqp : q + p = k) (U : Cᵒᵖ)
    (x : (E.X p).val.obj U) (y : (L.X q).val.obj U) :
    WeilConjectures.coefficientHomSectionEvaluation.{r, c, v} J R E L B
        (generalOrdinaryBidual.{c, v, r} J R E
          ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj B) ≫
          ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map a.op).app
            ((WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj B))
        p q k hqp U x y =
      (p * q).negOnePow •
        WeilConjectures.coefficientHomSectionEvaluation.{r, c, v} J R L E B
          a q p k hpq U y x := by
  let I := (WeilConjectures.coefficientHomResolution.{r, c, v} J R).obj B
  have hi := homComplexFunctor_map_f_π.{c, v, max c v r, max c v r} (R := R)
    a (𝟙 I) p q k hqp
  simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at hi
  have he := congrArg (fun f ↦
    ((f.val.app U (((generalOrdinaryBidual.{c, v, r} J R E I).f p).val.app U x)).app
      (op (Over.mk (𝟙 U.unop)))).hom y) hi
  simp only [WeilConjectures.coefficientHomSectionEvaluation,
    WeilConjectures.coefficientHomComponent, HomologicalComplex.comp_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at he ⊢
  erw [he]
  change (((homComplexπ.{c, v, max c v r, max c v r} (R := R)
    (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I p q k hqp).val.app U
      ((ringedSiteBidualDegree.{c, v, r} J R E I p).val.app U x)).app
        (op (Over.mk (𝟙 U.unop)))).hom ((a.f q).val.app U y) = _
  have hb := ringedSiteBidualDegree_eval.{c, v, r} J R E I p q k hqp U x
    (op (Over.mk (𝟙 U.unop))) ((a.f q).val.app U y)
  change _ = (p * q).negOnePow •
    (((homComplexπ.{c, v, max c v r, max c v r} (R := R) E I q p k hpq).val.app U
      ((a.f q).val.app U y)).app (op (Over.mk (𝟙 U.unop)))).hom
        ((E.X p).val.map (𝟙 U) x) at hb
  set_option backward.isDefEq.respectTransparency false in
  simpa only [PresheafOfModules.map_id, ModuleCat.restrictScalarsId',
    NatIso.ofComponents_inv_app, ModuleCat.restrictScalarsId'App_inv_apply] using hb

set_option backward.isDefEq.respectTransparency false in
private theorem resolvedBidual_normalization_kflat
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (E : Complex.{c, v, r} J R)
    (hE : CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := R) E) :
    let B := ringedSiteDualityUnitComplex.{c, v, r} J R
    let I := resolvedTarget.{c, v, r} J R B
    let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
    let U := SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := R) I
    let T := resolvedDual.{c, v, r, w} J R (Q.obj B)
    Q.map (generalOrdinaryBidual.{c, v, r} J R E I) ≫
        (doubleComparison Q U T (dualResolutionIso.{c, v, r, w} J R B) E).hom =
      ringedSiteBidual M.closed M.symmetric (Q.obj B) (Q.obj E) := by
  classical
  dsimp only
  let B := ringedSiteDualityUnitComplex.{c, v, r} J R
  let I := resolvedTarget.{c, v, r} J R B
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let U := SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := R) I
  let T := resolvedDual.{c, v, r, w} J R (Q.obj B)
  let α := dualResolutionIso.{c, v, r, w} J R B
  let b := generalOrdinaryBidual.{c, v, r} J R E I
  obtain ⟨L, a, hL, _, ha, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (U.obj (op E))
  let φ := b ≫ U.map a.op
  obtain ⟨ψa, hψa, hea⟩ := M.models.uncurry_model ⟨L, hL⟩ ⟨E, hE⟩ B a
  obtain ⟨ψφ, hψφ, heφ⟩ := M.models.uncurry_model ⟨E, hE⟩ ⟨L, hL⟩ B φ
  obtain ⟨σ, hσ, heσ⟩ := M.symmetry_model E L hE hL
  have hψ : ψφ = σ ≫ ψa := by
    apply totalTensor_generator_ext.{c, v, r} J R E L I
    intro p q k hpq V x y
    simp only [HomologicalComplex.comp_f, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply]
    calc
      _ = (p * q).negOnePow •
          WeilConjectures.coefficientHomSectionEvaluation.{r, c, v} J R L E B
            a q p k hpq V y x :=
        (hψφ p q k hpq (by omega) V x y).trans
          (bidual_precompose_formula.{c, v, r} J R E L B a p q k hpq (by omega) V x y)
      _ = (ψa.f k).val.app V ((p * q).negOnePow •
          WeilConjectures.coefficientTensorGenerator.{r, c, v} J R L E q p k
            (by omega) V y x) := by
        simp only [Units.smul_def, map_zsmul]
        rw [hψa q p k (by omega) hpq V y x]
      _ = _ := congrArg (fun z ↦ (ψa.f k).val.app V z)
        (hσ p q k hpq (by omega) V x y).symm
  let aa := Q.map a ≫ (α.app (op E)).hom
  let ff := Q.map φ ≫ (α.app (op L)).hom
  have hu : (M.closed.transpose (Q.obj E) (Q.obj L) (Q.obj B)).symm ff =
      (M.symmetric.braiding (Q.obj E) (Q.obj L)).hom ≫
        (M.closed.transpose (Q.obj L) (Q.obj E) (Q.obj B)).symm aa := by
    apply comparison_uncurry_square
      (M.models.iso J R M.closed E L hE hL)
      (M.models.iso J R M.closed L E hL hE)
      (M.symmetric.braiding (Q.obj E) (Q.obj L)).hom
      (Q.map σ) (Q.map ψa) (Q.map ψφ)
      (WeilConjectures.coefficientHomResolutionInverse.{r, c, v, w} J R B)
      _ _ heσ heφ hea
    rw [hψ, Q.map_comp]
  have hb : ringedSiteBidual M.closed M.symmetric (Q.obj B) (Q.obj E) ≫
      T.map aa.op = ff := by
    apply (M.closed.transpose (Q.obj E) (Q.obj L) (Q.obj B)).symm.injective
    erw [bidual_uncurry_square]
    exact hu.symm
  let : QuasiIso a := ha
  let : IsIso aa := by dsimp [aa, Q]; infer_instance
  apply (cancel_mono (T.map aa.op)).mp
  simpa only [Category.assoc] using
    (doubleComparison_source Q U T α E L a b).trans hb.symm

set_option backward.isDefEq.respectTransparency false in
private theorem resolvedBidual_normalization
    (M : RingedSiteDualityModel.{c, v, r, w} J R)
    (E : Complex.{c, v, r} J R) :
    let B := ringedSiteDualityUnitComplex.{c, v, r} J R
    let I := resolvedTarget.{c, v, r} J R B
    let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
    let U := SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := R) I
    let T := resolvedDual.{c, v, r, w} J R (Q.obj B)
    Q.map (generalOrdinaryBidual.{c, v, r} J R E I) ≫
        (doubleComparison Q U T (dualResolutionIso.{c, v, r, w} J R B) E).hom =
      ringedSiteBidual M.closed M.symmetric (Q.obj B) (Q.obj E) := by
  classical
  dsimp only
  let B := ringedSiteDualityUnitComplex.{c, v, r} J R
  let I := resolvedTarget.{c, v, r} J R B
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let U := SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := R) I
  let T := resolvedDual.{c, v, r, w} J R (Q.obj B)
  let α := dualResolutionIso.{c, v, r, w} J R B
  let b := fun E ↦ generalOrdinaryBidual.{c, v, r} J R E I
  obtain ⟨P, p, hP, _, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients E
  let : QuasiIso p := hp
  apply (cancel_epi (Q.map p)).mp
  calc
    _ = Q.map (b P) ≫ Q.map ((U.rightOp ⋙ U).map p) ≫
        (doubleComparison Q U T α E).hom := by
      rw [← Q.map_comp_assoc, ordinaryBidual_naturality, Q.map_comp, Category.assoc]
    _ = (Q.map (b P) ≫ (doubleComparison Q U T α P).hom) ≫
        (T.rightOp ⋙ T).map (Q.map p) := by
      rw [doubleComparison_naturality, Category.assoc]
    _ = ringedSiteBidual M.closed M.symmetric (Q.obj B) (Q.obj P) ≫
        (T.rightOp ⋙ T).map (Q.map p) := by
      rw [resolvedBidual_normalization_kflat.{c, v, r, w} J R M P hP]
    _ = _ := (ringedSiteBidual_naturality M.closed M.symmetric
      (Q.obj B) (Q.map p)).symm

omit [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)] in
set_option backward.isDefEq.respectTransparency false in
private theorem ordinaryBidual_signed_shift
    (I E : Complex.{c, v, r} J R)
    (s : ∀ (L : Complex.{c, v, r} J R) (m : ℤ),
      homComplex.{c, v, max c v r, max c v r} (R := R) (L⟦m⟧) I ≅
        (homComplex.{c, v, max c v r, max c v r} (R := R) L I)⟦-m⟧)
    (χ : (SignedDoubleHomCone.doubleDual.{c, v, r, max c v r} (R := R) I).obj (E⟦(1 : ℤ)⟧) ≅
      ((SignedDoubleHomCone.doubleDual.{c, v, r, max c v r} (R := R) I).obj E)⟦(1 : ℤ)⟧)
    (hχ : χ.hom = -((SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := R) I).map (s E 1).inv.op ≫
      (s (homComplex.{c, v, max c v r, max c v r} (R := R) E I) (-1)).hom))
    (hf : ∀ p t : ℤ,
      χ.hom.f p ≫
          (((SignedDoubleHomCone.doubleDual.{c, v, r, max c v r} (R := R)
            I).obj E).shiftFunctorObjXIso 1 p (p + 1) rfl).hom ≫
          SignedDoubleHomCone.proj.{c, v, r, max c v r} (R := R)
            (homComplex.{c, v, max c v r, max c v r} (R := R) E I)
            I (p + 1) t (t + (p + 1)) rfl =
        (p + t).negOnePow •
          (SignedDoubleHomCone.proj.{c, v, r, max c v r} (R := R)
            (homComplex.{c, v, max c v r, max c v r} (R := R) (E⟦(1 : ℤ)⟧) I)
            I p (t + 1) (t + (p + 1)) (by omega) ≫
            SheafOfModules.homObjMap (R := R)
              (SignedDoubleHomCone.reindexOne.{c, v, r, max c v r} (R := R) E I t) (𝟙 _))) :
    let U := SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := R) I
    generalOrdinaryBidual.{c, v, r} J R (E⟦(1 : ℤ)⟧) I ≫
        (-(U.map (s E 1).inv.op ≫ (s (U.obj (op E)) (-1)).hom)) =
      (generalOrdinaryBidual.{c, v, r} J R E I)⟦(1 : ℤ)⟧' := by
  have hb := ordinaryBidual_shift_with.{c, v, r} J R E I χ (by
    intro p t
    have hp := hf p t
    dsimp only [SignedDoubleHomCone.doubleDual, SignedDoubleHomCone.dual,
      homComplex, Functor.comp_obj, Functor.rightOp_obj, Functor.flip_obj_obj,
      unop_op] at hp ⊢
    simp only [SignedDoubleHomCone.proj, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp,
      CochainComplex.shiftFunctor_obj_X',
      CochainComplex.shiftFunctor_obj_X] at hp
    exact hp)
  rw [hχ] at hb
  exact hb

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation-transpose biduality commutes with the normalized degree-one comparison.
Source: Stacks 0A97 (lemma-internal-hom-evaluate), 08J9 (lemma-internal-hom), and
lem-sf-double-hom-cone-comparison.
(blueprint: lem-coef-bidual-evaluation-shift-one).
Proof: Resolve the coefficient unit by I and form the signed evaluation chain map
b_E(x)(f)=(-1)^(p*q)f(x). Its differential and degree-one shift identities are
checked on every Hom-product projection. For a K-flat E, resolve Hom(E,I) by a
K-flat L. The two normalized uncurrying squares and Koszul symmetry identify
Q(b_E) with the actual evaluation transpose, through the fixed double-Hom
comparison: both uncurried maps agree on all pure tensor generators. Naturality
and K-flat replacement extend the identification to every E. The inverse ordinary
signed source shift satisfies LeftFormula; its derived descent is sourceShift by
uniqueness of LeftNormalization. Transport the negative composite of its two
occurrences through the fixed representative isomorphisms. Naturality and essential
surjectivity of localization then give the displayed identity for every X. -/
theorem coefficientBidualEvaluation_shift_one
    (M : RingedSiteDualityModel.{c, v, r, w} J R) (X : D.{c, v, r, w} J R) :
    let O := ringedSiteDualityUnit.{c, v, r, w} J R
    let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
    let T := Prod.sectL _ O ⋙ H
    ringedSiteBidual M.closed M.symmetric O (X⟦(1 : ℤ)⟧) ≫
        (-(H.map (Prod.mkHom ((sourceShift.{c, v, r, w} J R X 1).hom.app O).op
          (𝟙 O)) ≫ (sourceShift.{c, v, r, w} J R (T.obj (op X)) (-1)).inv.app O)) =
      (ringedSiteBidual M.closed M.symmetric O X)⟦(1 : ℤ)⟧' := by
  classical
  let O := ringedSiteDualityUnit.{c, v, r, w} J R
  let B := ringedSiteDualityUnitComplex.{c, v, r} J R
  let Q : Complex.{c, v, r} J R ⥤ D.{c, v, r, w} J R := DerivedCategory.Q
  let I := resolvedTarget.{c, v, r} J R B
  obtain ⟨s, ξ, θ, hs, hn, hξ, hf, hfst, hsnd, hnat, hinr, hδ⟩ :=
    SignedDoubleHomCone.comparison.{c, v, r, max c v r} (R := R) I
  let U := SignedDoubleHomCone.dual.{c, v, r, max c v r} (R := R)
    (resolvedTarget.{c, v, r} J R B)
  let T := resolvedDual.{c, v, r, w} J R O
  let F := T.rightOp ⋙ T
  let α := dualResolutionIso.{c, v, r, w} J R B
  let κ (P : D.{c, v, r, w} J R) (m : ℤ) :=
    (sourceShift.{c, v, r, w} J R P m).app O
  have hκ (P P' : D.{c, v, r, w} J R) (f : P' ⟶ P) (m : ℤ) :
      (T.map f.op)⟦-m⟧' ≫ (κ P' m).hom =
        (κ P m).hom ≫ T.map (f⟦m⟧').op :=
    sourceShift_naturality.{c, v, r, w} J R P P' O f m
  let χ := doubleShiftNatTrans T κ hκ
  let δ : 𝟭 (D.{c, v, r, w} J R) ⟶ F :=
    { app P := ringedSiteBidual M.closed M.symmetric O P
      naturality _ _ f := ringedSiteBidual_naturality M.closed M.symmetric O f }
  have hEq : Functor.whiskerLeft (shiftFunctor (D.{c, v, r, w} J R) (1 : ℤ)) δ ≫ χ =
      Functor.whiskerRight δ (shiftFunctor (D.{c, v, r, w} J R) (1 : ℤ)) := by
    apply natTrans_ext_on_essSurj Q
    intro E
    have hc := doubleShift_compare Q U T α
      s κ
      (fun P L eP m ↦ sourceShift_signed.{c, v, r, w} J R P L B eP m
        (s L m).symm
        (signedHomShift_inv_formula.{c, v, r} J R I L m (s L m) (hs L m))) E
    have hb := ordinaryBidual_signed_shift.{c, v, r} J R I E s (ξ E) (hξ E) (hf E)
    have hn := (Q.commShiftIso (1 : ℤ)).hom.naturality
      (generalOrdinaryBidual.{c, v, r} J R E (resolvedTarget.{c, v, r} J R B))
    have hd := δ.naturality ((Q.commShiftIso (1 : ℤ)).hom.app E)
    simp only [Functor.id_map, Functor.comp_obj] at hd
    apply (cancel_epi ((Q.commShiftIso (1 : ℤ)).hom.app E)).mp
    change _ ≫ δ.app ((Q.obj E)⟦(1 : ℤ)⟧) ≫ χ.app (Q.obj E) =
      _ ≫ (δ.app (Q.obj E))⟦(1 : ℤ)⟧'
    rw [← Category.assoc, hd, Category.assoc]
    change ringedSiteBidual M.closed M.symmetric O (Q.obj (E⟦(1 : ℤ)⟧)) ≫
      F.map ((Q.commShiftIso (1 : ℤ)).hom.app E) ≫ χ.app (Q.obj E) = _
    erw [← resolvedBidual_normalization.{c, v, r, w} J R M (E⟦(1 : ℤ)⟧)]
    simp only [Category.assoc]
    change Q.map (generalOrdinaryBidual.{c, v, r} J R (E⟦(1 : ℤ)⟧)
      (resolvedTarget.{c, v, r} J R B)) ≫ _ = _
    erw [← hc]
    rw [← Q.map_comp_assoc, hb]
    simp only [Functor.comp_map] at hn
    erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
    exact congrArg (fun f : Q.obj E ⟶ F.obj (Q.obj E) ↦
      (Q.commShiftIso (1 : ℤ)).hom.app E ≫ f⟦(1 : ℤ)⟧')
      (resolvedBidual_normalization.{c, v, r, w} J R M E)
  have h := congrArg (fun t ↦ t.app X) hEq
  simpa [δ, χ, doubleShiftNatTrans, κ, T, resolvedDual, O] using h

end CategoryTheory
