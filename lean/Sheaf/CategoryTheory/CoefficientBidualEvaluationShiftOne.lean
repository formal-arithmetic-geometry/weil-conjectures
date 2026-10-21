/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
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
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.RingedHomUniverses
attribute [local irreducible] CategoryTheory.homComplexFunctor
/- The ordinary signed evaluation is a genuine chain map for every coefficient target I.
The following checked calculation retains the target differential and cancels its two terms.
The ordinary degree-one shift identity is checked against SignedDoubleHomCone.comparison.
Identification with the derived transpose and descent remain in the named source theorem below. -/
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
private theorem unsignedReindex_proj (E I : RingedSiteComplex.{c, v, r} J R)
    (t p b : ℤ) (h : p + (t + 1) = b) :
    SignedDoubleHomCone.reindexOne.{c, v, max c v r, max c v r} E I t ≫
        homComplexπ.{c, v, max c v r, max c v r} (R := R) (E⟦(1 : ℤ)⟧) I
          (t + 1) p b h =
      homComplexπ.{c, v, max c v r, max c v r} (R := R) E I t (p + 1) b (by omega) ≫
        SheafOfModules.homObjMap (R := R)
          (E.shiftFunctorObjXIso 1 p (p + 1) rfl).hom (𝟙 _) := by
  subst b
  exact Fan.IsLimit.fac (SignedDoubleHomCone.productLimit _ I (t + 1)) _ p
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
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
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
private theorem ordinaryBidual_shift_one (I : RingedSiteComplex.{c, v, r} J R) :
    ∃ χ : ∀ E : RingedSiteComplex.{c, v, r} J R,
      homComplex.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) (E⟦(1 : ℤ)⟧) I) I ≅
      (homComplex.{c, v, max c v r, max c v r} (R := R)
        (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I)⟦(1 : ℤ)⟧,
      (∀ (E : RingedSiteComplex.{c, v, r} J R) (p t : ℤ),
        (χ E).hom.f p ≫ homComplexπ.{c, v, max c v r, max c v r} (R := R)
          (homComplex.{c, v, max c v r, max c v r} (R := R) E I) I
          (p + 1) t (t + (p + 1)) rfl =
        (p + t).negOnePow •
          (homComplexπ.{c, v, max c v r, max c v r} (R := R)
            (homComplex.{c, v, max c v r, max c v r} (R := R) (E⟦(1 : ℤ)⟧) I) I
            p (t + 1) (t + (p + 1)) (by omega) ≫
              SheafOfModules.homObjMap (R := R)
                (SignedDoubleHomCone.reindexOne.{c, v, max c v r, max c v r} E I t) (𝟙 _))) ∧
      ∀ E : RingedSiteComplex.{c, v, r} J R,
        generalOrdinaryBidual.{c, v, r} J R (E⟦(1 : ℤ)⟧) I ≫ (χ E).hom =
          (generalOrdinaryBidual.{c, v, r} J R E I)⟦(1 : ℤ)⟧' := by
  obtain ⟨s, χ, θ, hs, hn, hdef, hf, hfst, hsnd, hnat, hinr, hδ⟩ :=
    SignedDoubleHomCone.comparison.{c, v, max c v r, max c v r} I
  refine ⟨χ, ?_, ?_⟩
  · intro E p t
    simpa only [SignedDoubleHomCone.proj, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, Category.comp_id,
      CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_obj_X] using
        hf E p t
  · intro E
    apply ordinaryBidual_shift_with.{c, v, r} J R E I (χ E)
    intro p t
    simpa only [SignedDoubleHomCone.proj, CochainComplex.shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, Category.comp_id,
      CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctor_obj_X] using
        hf E p t

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

private def generalOrdinaryBidualTransformation (I : RingedSiteComplex.{c, v, r} J R) :
    𝟭 (RingedSiteComplex.{c, v, r} J R) ⟶
      SignedDoubleHomCone.doubleDual.{c, v, max c v r, max c v r} I where
  app E := generalOrdinaryBidual.{c, v, r} J R E I
  naturality _ _ f := ordinaryBidual_naturality.{c, v, r} J R I f

end CategoryTheory

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
  [HasDerivedCategory.{w} (Modules.{c, v, r} J R)]

/-- Evaluation-transpose biduality commutes with the normalized degree-one comparison.
Source: Stacks 0A97 (lemma-internal-hom-evaluate), 08J9 (lemma-internal-hom), and
lem-sf-double-hom-cone-comparison.
(blueprint: lem-coef-bidual-evaluation-shift-one).
Proof: Represent O by a K-injective I. For every complex E the chain evaluation is
b_E(x)(f)=(-1)^(p*q)f(x), with x of degree p and f of degree q. The Hom differential
shows this is a chain map: the two terms involving d_I cancel and the remaining term is
(-1)^((p+1)*q)f(dx). On a K-flat representative P, resolve Hom(P,I) by a K-flat L with
map a:L -> Hom(P,I). The normalized tensor-Hom adjunction and Koszul symmetry represent
the defining evaluation transpose by Hom(a,I) composed with b_P. Hom(a,I) is a
quasi-isomorphism, so the derived evaluation is Q(b_P); naturality and a K-flat replacement
extend this identification to every E. Now let x lie in E[1]^p=E^(p+1) and let f have
unshifted Hom degree t. The signed double-Hom comparison contributes (-1)^(p+t), and
b_(E[1]) contributes (-1)^(p*(t+1)). Their product equals (-1)^((p+1)*t), because the
exponents differ by 2*p. This is precisely b_E[1]. The fixed representative comparisons
therefore give the displayed derived equality for every X. Only degree one is asserted;
coherent extension to other shifts is a separate categorical argument. -/
theorem coefficientBidualEvaluation_shift_one
    (M : RingedSiteDualityModel.{c, v, r, w} J R) (X : D.{c, v, r, w} J R) :
    let O := ringedSiteDualityUnit.{c, v, r, w} J R
    let H := derivedInternalHomOfUniverses.{c, v, r, w} J R
    let T := Prod.sectL _ O ⋙ H
    ringedSiteBidual M.closed M.symmetric O (X⟦(1 : ℤ)⟧) ≫
        (-(H.map (Prod.mkHom ((sourceShift.{c, v, r, w} J R X 1).hom.app O).op
          (𝟙 O)) ≫ (sourceShift.{c, v, r, w} J R (T.obj (op X)) (-1)).inv.app O)) =
      (ringedSiteBidual M.closed M.symmetric O X)⟦(1 : ℤ)⟧' := by
  sorry

end CategoryTheory
