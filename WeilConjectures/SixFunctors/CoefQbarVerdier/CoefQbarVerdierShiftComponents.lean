/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import all WeilConjectures.SixFunctors.CoefQbarVerdier.CoefQbarVerdierEvaluationDescent
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierSignedEvaluationShift
import WeilConjectures.SixFunctors.RationalVerdier.RationalTensorStageShiftCancellation
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierEvaluationDetection

/-! # Explicit finite-stage components of the Verdier shift comparison

Source: thm-coef-qbar-verdier, proof steps 3--4. The finite shifts must be chosen
compatibly with the normalized evaluation transposes before they can descend.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

private theorem opComp_commShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) [F.CommShift ℤ] [G.CommShift ℤ] :
    NatTrans.CommShift (Functor.opComp F G).hom ℤ := by
  constructor
  intro n
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.opComp, Iso.refl_hom, NatTrans.id_app, Functor.comp_obj,
    (shiftFunctor Eᵒᵖ n).map_id, Category.comp_id, Category.id_comp]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.op_commShiftIso_hom_app
    _ _ n (-n) (add_neg_cancel n), Functor.commShiftIso_comp_inv_app,
    Functor.comp_map, Functor.op_map, op_comp, Category.assoc]
  simp only [unop_comp, Quiver.Hom.unop_op, Functor.map_comp, op_comp,
    Functor.op_obj, Category.assoc]
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op, Category.assoc]
  simp only [← G.map_comp_assoc, Iso.unop_hom_inv_id_app_assoc]
  rfl

private theorem compatibility_paste
    {C D A : Type*} [Category C] [Category D] [Category A]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift A ℤ]
    (d : Cᵒᵖ ⥤ C) (e : Dᵒᵖ ⥤ D) [d.CommShift ℤ] [e.CommShift ℤ]
    (T : C ⥤ D) [T.CommShift ℤ] (J : C ⥤ A) [J.CommShift ℤ]
    (K : D ⥤ A) [K.CommShift ℤ] (V : Aᵒᵖ ⥤ A)
    (s : T ⋙ K ≅ J) [NatTrans.CommShift s.hom ℤ]
    (b : d ⋙ T ≅ T.op ⋙ e) [NatTrans.CommShift b.hom ℤ]
    (rJ : d ⋙ J ≅ J.op ⋙ V) (rK : e ⋙ K ≅ K.op ⋙ V)
    [(J.op ⋙ V).CommShift ℤ] [(K.op ⋙ V).CommShift ℤ]
    [NatTrans.CommShift rJ.hom ℤ] [NatTrans.CommShift rK.hom ℤ]
    (ht : ∀ P : C,
      K.map (b.hom.app (op P)) ≫ rK.hom.app (op (T.obj P)) ≫
          V.map (s.inv.app P).op = s.hom.app (d.obj (op P)) ≫ rJ.hom.app (op P)) :
    letI : ((T.op ⋙ K.op) ⋙ V).CommShift ℤ :=
      Functor.CommShift.ofIso (Functor.associator T.op K.op V).symm ℤ
    NatTrans.CommShift
      (Functor.whiskerRight ((NatIso.op s ≪≫ Functor.opComp T K).hom) V) ℤ := by
  letI : ((T.op ⋙ K.op) ⋙ V).CommShift ℤ :=
    Functor.CommShift.ofIso (Functor.associator T.op K.op V).symm ℤ
  haveI : NatTrans.CommShift (Functor.associator T.op K.op V).inv ℤ :=
    Functor.CommShift.ofIso_compatibility (Functor.associator T.op K.op V).symm ℤ
  let r : J.op ⋙ V ≅ (T.op ⋙ K.op) ⋙ V :=
    rJ.symm ≪≫ Functor.isoWhiskerLeft d s.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight b K ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft T.op rK ≪≫
      (Functor.associator _ _ _).symm
  have hr : NatTrans.CommShift r.hom ℤ := by
    dsimp only [r, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  have heq : Functor.whiskerRight
      ((NatIso.op s ≪≫ Functor.opComp T K).hom) V = r.hom := by
    ext P
    dsimp only [r]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      NatIso.op_hom, NatTrans.op_app, Functor.opComp, Iso.refl_hom,
      Category.id_comp, Category.comp_id]
    apply (cancel_epi (rJ.hom.app P)).1
    apply (cancel_mono (V.map (s.inv.app P.unop).op)).1
    simp only [Category.assoc, ← V.map_comp, ← op_comp, Iso.inv_hom_id_app,
      op_id]
    apply (cancel_epi (s.hom.app (d.obj P))).1
    simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    erw [V.map_id, Category.comp_id]
    simpa only [Functor.comp_obj, Functor.op_obj, op_unop, Category.assoc]
      using (ht P.unop).symm
  rw [heq]
  exact hr

private theorem restrictionShift_naturality
    {C A B : Type*} [Category C] [Category A] [Category B]
    [HasShift C ℤ] [HasShift A ℤ] [HasShift B ℤ]
    (J K : C ⥤ A) [J.CommShift ℤ] [K.CommShift ℤ]
    (V : A ⥤ B) [cJ : (J ⋙ V).CommShift ℤ] [cK : (K ⋙ V).CommShift ℤ]
    (e : J ≅ K) [NatTrans.CommShift e.hom ℤ]
    [NatTrans.CommShift (Functor.whiskerRight e.hom V) ℤ] (n : ℤ) (X : C) :
    V.map ((e.hom.app X)⟦n⟧') ≫
        V.map ((K.commShiftIso n).inv.app X) ≫ (cK.commShiftIso n).hom.app X =
      (V.map ((J.commShiftIso n).inv.app X) ≫ (cJ.commShiftIso n).hom.app X) ≫
        (V.map (e.hom.app X))⟦n⟧' := by
  have he := NatTrans.shift_app_comm e.hom n X
  have hv := NatTrans.shift_app_comm (Functor.whiskerRight e.hom V) n X
  dsimp only [Functor.whiskerRight_app, Functor.comp_obj] at hv
  apply (cancel_epi (V.map ((J.commShiftIso n).hom.app X))).1
  simp only [Category.assoc, ← V.map_comp_assoc]
  rw [← Category.assoc, he]
  simp only [Category.assoc, Iso.hom_inv_id_app,
    V.map_comp, V.map_id, Category.id_comp]
  erw [V.map_id, Category.id_comp]
  exact hv.symm

private theorem restrictionShift_precomp
    {C' C A B : Type*} [Category C'] [Category C] [Category A] [Category B]
    [HasShift C' ℤ] [HasShift C ℤ] [HasShift A ℤ] [HasShift B ℤ]
    (T : C' ⥤ C) [T.CommShift ℤ] (J : C ⥤ A) [J.CommShift ℤ]
    (V : A ⥤ B) [c : (J ⋙ V).CommShift ℤ] (n : ℤ) (X : C') :
    letI : ((T ⋙ J) ⋙ V).CommShift ℤ :=
      Functor.CommShift.ofIso (Functor.associator T J V).symm ℤ
    V.map (((T ⋙ J).commShiftIso n).inv.app X) ≫
        (((T ⋙ J) ⋙ V).commShiftIso n).hom.app X =
      V.map ((J.commShiftIso n).inv.app (T.obj X)) ≫
        (c.commShiftIso n).hom.app (T.obj X) := by
  simp only [Functor.commShiftIso_comp_inv_app,
    Functor.CommShift.ofIso_commShiftIso_hom_app,
    Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.comp_obj,
    Iso.symm_inv, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app,
    Category.id_comp, V.map_comp, Category.assoc]
  erw [(shiftFunctor B n).map_id, Category.comp_id]
  try simp only [V.map_comp, Category.assoc]
  rw [← V.map_comp_assoc (J.map ((T.commShiftIso n).inv.app X))
    (J.map ((T.commShiftIso n).hom.app X))]
  simp only [← J.map_comp, Iso.inv_hom_id_app, J.map_id, V.map_id, Category.id_comp]

private theorem restrictionShift_transition
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift A ℤ] [HasShift B ℤ]
    (T : C ⥤ D) [T.CommShift ℤ] (J : C ⥤ A) [J.CommShift ℤ]
    (K : D ⥤ A) [K.CommShift ℤ] (V : A ⥤ B)
    [cJ : (J ⋙ V).CommShift ℤ] [cK : (K ⋙ V).CommShift ℤ]
    (e : J ≅ T ⋙ K) [NatTrans.CommShift e.hom ℤ]
    (he : letI : ((T ⋙ K) ⋙ V).CommShift ℤ :=
      Functor.CommShift.ofIso (Functor.associator T K V).symm ℤ
      NatTrans.CommShift (Functor.whiskerRight e.hom V) ℤ)
    (n : ℤ) (X : C) :
    V.map ((e.hom.app X)⟦n⟧') ≫
        V.map ((K.commShiftIso n).inv.app (T.obj X)) ≫
          (cK.commShiftIso n).hom.app (T.obj X) =
      (V.map ((J.commShiftIso n).inv.app X) ≫ (cJ.commShiftIso n).hom.app X) ≫
        (V.map (e.hom.app X))⟦n⟧' := by
  let : ((T ⋙ K) ⋙ V).CommShift ℤ :=
    Functor.CommShift.ofIso (Functor.associator T K V).symm ℤ
  let := he
  have h := restrictionShift_naturality J (T ⋙ K) V e n X
  rw [Category.assoc, restrictionShift_precomp T K V n X] at h
  simpa only [Category.assoc] using h

end CategoryTheory

namespace CategoryTheory.StageSystem

private theorem opStageComparison_naturality
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] {B : Type*} [Category B]
    (S : StageSystem C) (G H : S.PairCategoryᵒᵖ ⥤ B)
    (e : ∀ i, (S.ι i).op ⋙ G ⟶ (S.ι i).op ⋙ H)
    (he : ∀ (A : S.PairCategory) (i : I) (h : A.stage ≤ i),
      G.map (S.isoToStage A h).inv.op ≫ (e i).app (op (A.toStage h)) =
        (e A.stage).app (op A.obj) ≫ H.map (S.isoToStage A h).inv.op)
    {A A' : S.PairCategoryᵒᵖ} (f : A ⟶ A') :
    G.map f ≫ (e A'.unop.stage).app (op A'.unop.obj) =
      (e A.unop.stage).app (op A.unop.obj) ≫ H.map f := by
  have hright (P : S.PairCategory) (i : I) (h : P.stage ≤ i) :
      G.map (S.isoToStage P h).hom.op ≫ (e P.stage).app (op P.obj) =
        (e i).app (op (P.toStage h)) ≫ H.map (S.isoToStage P h).hom.op := by
    apply (cancel_epi (G.map (S.isoToStage P h).inv.op)).1
    dsimp only [Functor.comp_obj, Functor.op_obj, StageSystem.ι_obj] at *
    erw [← G.map_comp_assoc, ← op_comp, Iso.hom_inv_id, op_id,
      G.map_id, Category.id_comp]
    erw [← Category.assoc, he P i h]
    erw [Category.assoc, ← H.map_comp, ← op_comp, Iso.hom_inv_id, op_id,
      H.map_id, Category.comp_id]
  have hf : f = f.unop.op := rfl
  rw [hf]
  generalize f.unop = g
  induction g using StageSystem.PairCategory.hom_induction with
  | h i hA' hA g =>
    rw [StageSystem.mkHom_eq_isoToStage hA' hA g]
    simp only [op_comp, Functor.map_comp]
    dsimp only [Functor.comp_obj, Functor.op_obj, StageSystem.ι_obj] at *
    simp only [Functor.map_comp]
    erw [Category.assoc, Category.assoc]
    have hn := (e i).naturality g.op
    dsimp only [Functor.comp_map, Functor.op_map] at hn
    erw [hright, reassoc_of% hn]
    erw [← Category.assoc, he A.unop i hA]
    simp only [Quiver.Hom.unop_op]
    erw [Category.assoc, Category.assoc]
    rfl

end CategoryTheory.StageSystem

namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open GeneralAlgebraicallyClosedCoefficients (Stage inclusion stageSystem)
open AlgebraicallyClosedCoefficients (Index Coefficient)
attribute [local irreducible] ScalarLocalization.category
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
  GeneralAlgebraicallyClosedCoefficients.pairCategory CategoryTheory.uniformProd
attribute [local implicit_reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  CategoryTheory.StageSystem.ι

/-- Transport the finite dual shift along its specified inclusion comparison. -/
@[irreducible] def finiteRestrictionShift (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    ((inclusion (Y := X) E).op ⋙ descendedDual D l hl Ω X F hF).CommShift ℤ := by
  letI : ((F.datum E).dual ⋙ inclusion (Y := X) E).CommShift ℤ :=
    @Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual (inclusion (Y := X) E)
      ℤ _ _ _ _ (t E) (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
  exact Functor.CommShift.ofIso (descendedComparison D l hl Ω X F hF E) ℤ

/-- Transport along the specified comparison makes that comparison commute with shifts. -/
theorem finiteRestrictionShift_compatibility (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    let cA : ((F.datum E).dual ⋙ inclusion (Y := X) E).CommShift ℤ :=
      @Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual (inclusion (Y := X) E)
        ℤ _ _ _ _ (t E) (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E)
    @NatTrans.CommShift _ _ _ _ _ _
      (descendedComparison D l hl Ω X F hF E).hom ℤ _ _ _ cA
      (finiteRestrictionShift D l hl Ω X F hF t E) := by
  unfold finiteRestrictionShift
  exact @Functor.CommShift.ofIso_compatibility _ _ _ _ _ _
    (descendedComparison D l hl Ω X F hF E) ℤ _ _ _
    (@Functor.CommShift.comp _ _ _ _ _ _ (F.datum E).dual (inclusion (Y := X) E)
      ℤ _ _ _ _ (t E) (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift E))

/-- The only possible shift component at a pair, prescribed by its finite stage.
The inverse inclusion comparison first moves the shifted pair back to its stage. -/
def shiftComponent (F : Finite D l hl Ω X) (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (n : ℤ) (P : (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ) :
    (descendedDual D l hl Ω X F hF).obj (P⟦n⟧) ≅
      ((descendedDual D l hl Ω X F hF).obj P)⟦n⟧ :=
  let J := (inclusion (Y := X) P.unop.stage).op
  let V := descendedDual D l hl Ω X F hF
  letI := finiteRestrictionShift D l hl Ω X F hF t P.unop.stage
  (V.mapIso ((J.commShiftIso n).app (op P.unop.obj))).symm ≪≫
    ((J ⋙ V).commShiftIso n).app (op P.unop.obj)

private def restrictedShiftIso (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (n : ℤ) (E : AlgebraicallyClosedCoefficients.Index l Ω) :
    (inclusion (Y := X) E).op ⋙
        (shiftFunctor _ n ⋙ descendedDual D l hl Ω X F hF) ≅
      (inclusion (Y := X) E).op ⋙
        (descendedDual D l hl Ω X F hF ⋙ shiftFunctor _ n) :=
  let J := (inclusion (Y := X) E).op
  let V := descendedDual D l hl Ω X F hF
  letI := finiteRestrictionShift D l hl Ω X F hF t E
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (J.commShiftIso n).symm V ≪≫
    Functor.associator _ _ _ ≪≫ (J ⋙ V).commShiftIso n ≪≫
    Functor.associator _ _ _

private theorem restrictedShiftIso_hom (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (n : ℤ) (E : AlgebraicallyClosedCoefficients.Index l Ω) (K : Stage l Ω X E) :
    (restrictedShiftIso D l hl Ω X F hF t n E).hom.app (op K) =
      (shiftComponent D l hl Ω X F hF t n (op ((inclusion E).obj K))).hom := by
  dsimp only [restrictedShiftIso, shiftComponent,
    GeneralAlgebraicallyClosedCoefficients.inclusion, CategoryTheory.StageSystem.ι,
    Functor.comp_obj, Functor.op_obj, op_unop]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.mapIso_inv,
    Functor.associator_hom_app,
    Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  exact rfl

private theorem shiftComponent_naturality_of_transitions (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (ht : ∀ (n : ℤ)
      (P : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).PairCategory)
      (E : AlgebraicallyClosedCoefficients.Index l Ω) (h : P.stage ≤ E),
      let a := ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).isoToStage P h).inv.op
      (descendedDual D l hl Ω X F hF).map (a⟦n⟧') ≫
          (shiftComponent D l hl Ω X F hF t n (op ((inclusion E).obj (P.toStage h)))).hom =
        (shiftComponent D l hl Ω X F hF t n (op P)).hom ≫
          ((descendedDual D l hl Ω X F hF).map a)⟦n⟧') :
    ∀ (n : ℤ) (P Q : (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ)
      (f : P ⟶ Q),
      (descendedDual D l hl Ω X F hF).map (f⟦n⟧') ≫
          (shiftComponent D l hl Ω X F hF t n Q).hom =
        (shiftComponent D l hl Ω X F hF t n P).hom ≫
          ((descendedDual D l hl Ω X F hF).map f)⟦n⟧' := by
  intro n P Q f
  let V := descendedDual D l hl Ω X F hF
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X
  have h := CategoryTheory.StageSystem.opStageComparison_naturality S
    (shiftFunctor _ n ⋙ V) (V ⋙ shiftFunctor _ n)
    (fun E ↦ (restrictedShiftIso D l hl Ω X F hF t n E).hom)
  have he : ∀ (A : S.PairCategory) (E : AlgebraicallyClosedCoefficients.Index l Ω)
      (hA : A.stage ≤ E),
      (shiftFunctor _ n ⋙ V).map (S.isoToStage A hA).inv.op ≫
          (restrictedShiftIso D l hl Ω X F hF t n E).hom.app (op (A.toStage hA)) =
        (restrictedShiftIso D l hl Ω X F hF t n A.stage).hom.app (op A.obj) ≫
          (V ⋙ shiftFunctor _ n).map (S.isoToStage A hA).inv.op := by
    intro A E hA
    simpa only [restrictedShiftIso_hom, Functor.comp_map, V, S,
      GeneralAlgebraicallyClosedCoefficients.inclusion, CategoryTheory.StageSystem.ι,
      Functor.comp_obj, Functor.op_obj] using ht n A E hA
  simpa only [restrictedShiftIso_hom, Functor.comp_map, V, S,
    GeneralAlgebraicallyClosedCoefficients.inclusion, CategoryTheory.StageSystem.ι,
    Functor.comp_obj, Functor.op_obj, op_unop] using h he f

private theorem shiftComponent_naturality_of_beta (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F)
    (t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω, (F.datum E).dual.CommShift ℤ)
    (hb : ∀ {E L : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ L),
      letI := t E
      letI := t L
      letI : ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h).CommShift ℤ :=
        GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
      let cE : ((F.datum E).dual ⋙ (stageSystem l Ω X).T h).CommShift ℤ :=
        @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _ (t E)
          (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h)
      let cL : (((stageSystem l Ω X).T h).op ⋙ (F.datum L).dual).CommShift ℤ :=
        @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
          (@commShiftFunctorOpInt _ _ _ _ _ _ _
            (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h))
          (t L)
      @NatTrans.CommShift _ _ _ _ _ _
        (q3_finiteDualStageComparison D l hl Ω X F h).hom ℤ _ _ _ cE cL) :
    ∀ (n : ℤ) (P Q : (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ)
      (f : P ⟶ Q),
      (descendedDual D l hl Ω X F hF).map (f⟦n⟧') ≫
          (shiftComponent D l hl Ω X F hF t n Q).hom =
        (shiftComponent D l hl Ω X F hF t n P).hom ≫
          ((descendedDual D l hl Ω X F hF).map f)⟦n⟧' := by
  apply shiftComponent_naturality_of_transitions D l hl Ω X F hF t
  intro n P L h
  cases P with
  | mk E M =>
  let P : (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).PairCategory := ⟨E, M⟩
  let S := GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X
  letI : HasShift S.PairCategory ℤ :=
    GeneralAlgebraicallyClosedCoefficients.hasShift (l := l) (Ω := Ω) (Y := X)
  let T := S.T h
  letI : T.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X P.stage L h
  let J := inclusion (Y := X) P.stage
  let K := inclusion (Y := X) L
  letI : J.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.inclusionCommShift P.stage
  letI : K.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.inclusionCommShift L
  let V := descendedDual D l hl Ω X F hF
  letI := t P.stage
  letI := t L
  have hb' := hb h
  let s := S.transIso h
  haveI : NatTrans.CommShift s.hom ℤ :=
    GeneralAlgebraicallyClosedCoefficients.transitionIso_commShift _ _ _
  let e : J.op ≅ T.op ⋙ K.op := NatIso.op s ≪≫ Functor.opComp T K
  haveI : NatTrans.CommShift (Functor.opComp T K).hom ℤ :=
    CategoryTheory.opComp_commShift T K
  haveI heop : NatTrans.CommShift e.hom ℤ := by
    dsimp only [e, Iso.trans_hom, NatIso.op_hom]
    infer_instance
  letI : (J.op ⋙ V).CommShift ℤ := finiteRestrictionShift D l hl Ω X F hF t P.stage
  letI : (K.op ⋙ V).CommShift ℤ := finiteRestrictionShift D l hl Ω X F hF t L
  have hrJ := finiteRestrictionShift_compatibility D l hl Ω X F hF t P.stage
  have hrK := finiteRestrictionShift_compatibility D l hl Ω X F hF t L
  have he := @CategoryTheory.compatibility_paste
    (sfRationalConstructibleCategory l (Coefficient.{u} l Ω P.stage) X)
    (sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) X)
    (generalAlgebraicallyClosedConstructibleCategory l Ω X) _ _ _ _ _ _
    (F.datum P.stage).dual (F.datum L).dual (t P.stage) (t L)
    T (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X P.stage L h)
    J (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift P.stage)
    K (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift L) V s
    (GeneralAlgebraicallyClosedCoefficients.transitionIso_commShift P.stage L h)
    (q3_finiteDualStageComparison D l hl Ω X F h) hb'
    (descendedComparison D l hl Ω X F hF P.stage)
    (descendedComparison D l hl Ω X F hF L)
    (finiteRestrictionShift D l hl Ω X F hF t P.stage)
    (finiteRestrictionShift D l hl Ω X F hF t L) hrJ hrK
    (q3_descendedComparison_transition D l hl Ω X F hF h)
  have hh := @CategoryTheory.restrictionShift_transition
    (sfRationalConstructibleCategory l (Coefficient.{u} l Ω P.stage) X)ᵒᵖ
    (sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) X)ᵒᵖ
    (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ
    (generalAlgebraicallyClosedConstructibleCategory l Ω X) _ _ _ _
    (inferInstance : HasShift
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω P.stage) X)ᵒᵖ ℤ)
    (inferInstance : HasShift
      (sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) X)ᵒᵖ ℤ)
    (inferInstance : HasShift
      (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ ℤ)
    (GeneralAlgebraicallyClosedCoefficients.hasShift (l := l) (Ω := Ω) (Y := X))
    T.op (@commShiftFunctorOpInt _ _ _ _ _ _ T
      (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X P.stage L h))
    J.op (@commShiftFunctorOpInt _ _ _ _ _ _ J
      (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift P.stage))
    K.op (@commShiftFunctorOpInt _ _ _ _ _ _ K
      (GeneralAlgebraicallyClosedCoefficients.inclusionCommShift L)) V
    (finiteRestrictionShift D l hl Ω X F hF t P.stage)
    (finiteRestrictionShift D l hl Ω X F hF t L) e heop he n (op P.obj)
  dsimp only [shiftComponent, Functor.comp_obj, Functor.op_obj] at hh ⊢
  convert hh using 1 <;>
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
      e, s, J, K, T, S, V, NatIso.op_hom, NatTrans.op_app, Functor.opComp,
      Iso.refl_hom, Category.comp_id, Category.assoc, StageSystem.transIso_hom_app,
      StageSystem.ι, Functor.comp_obj, Iso.app_hom, Iso.app_inv,
      StageSystem.PairCategory.toStage, P] <;> rfl

/-- The normalized finite beta preserves the signed exact dual shifts. Evaluation
injectivity turns the scalar tensor cancellation square into this Hom square. -/
private theorem signedShift_stageComparison (F : Finite D l hl Ω X)
    {E L : Index l Ω} (h : E ≤ L) :
    letI := RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω E)
      (F.omega E) (F.datum E)
    letI := RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω L)
      (F.omega L) (F.datum L)
    letI : ((stageSystem l Ω X).T h).CommShift ℤ :=
      GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
    let cE : ((F.datum E).dual ⋙ (stageSystem l Ω X).T h).CommShift ℤ :=
      @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        (RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω E)
          (F.omega E) (F.datum E))
        (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h)
    let cL : (((stageSystem l Ω X).T h).op ⋙ (F.datum L).dual).CommShift ℤ :=
      @Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        (@commShiftFunctorOpInt _ _ _ _ _ _ _
          (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h))
        (RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω L)
          (F.omega L) (F.datum L))
    @NatTrans.CommShift _ _ _ _ _ _
      (q3_finiteDualStageComparison D l hl Ω X F h).hom ℤ _ _ _ cE cL := by
  letI := RationalVerdier.units D l hl X
  let T := (stageSystem l Ω X).T h
  letI : T.CommShift ℤ :=
    GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
  letI := RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω E)
    (F.omega E) (F.datum E)
  letI := RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω L)
    (F.omega L) (F.datum L)
  exact @commShift_of_reindexed_components _ _ _ _ _ _ T
    (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h)
    (F.datum E).dual (F.datum L).dual
    (RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω E)
      (F.omega E) (F.datum E))
    (RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω L)
      (F.omega L) (F.datum L))
    (q3_finiteDualStageComparison D l hl Ω X F h).hom (by
  intro n K
  apply @evaluation_shift_transport _ _ _ _ _ _
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω E))
    (RationalVerdier.tensor D l hl X (Coefficient.{u} l Ω L)) T
    (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h)
    (F.datum E).dual (F.datum L).dual _ _
    (F.datum E).evaluation (F.datum L).evaluation
    (fun K P f g hh ↦ RationalVerdier.rational_evaluation_detect D l hl X
      (Coefficient.{u} l Ω L) (F.omega L) (F.datum L) K P f g hh)
    (fun {_ _} f ↦ (F.datum L).evaluation_natural _ _ f)
    (rationalTensorStageComparison l Ω X h)
    ((operationStageTransitionIso l Ω X E L h).hom.app
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        (F.omega E).omega) ≫ (F.scalar E L h).omega.hom)
    (q3_finiteDualStageComparison D l hl Ω X F h).hom
    (fun K ↦ by
      dsimp only [Functor.comp_obj, Functor.op_obj]
      simp only [q3_finiteDualStageComparison_hom, T, Functor.op_obj]
      convert finite_evaluation_scalar_of_stages D l hl Ω X F h K using 1
      rfl)
    n (@reindexedDualShift _ _ _ (F.datum E).dual
      (RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω E)
        (F.omega E) (F.datum E)) n)
    (@reindexedDualShift _ _ _ (F.datum L).dual
      (RationalVerdier.signedShift D l hl X (Coefficient.{u} l Ω L)
        (F.omega L) (F.datum L)) n)
    (fun K P ↦ RationalVerdier.signedOppositeShift D l hl X
      (Coefficient.{u} l Ω E) K P n)
    (fun K P ↦ RationalVerdier.signedOppositeShift D l hl X
      (Coefficient.{u} l Ω L) K P n)
    (fun K {_ _} f ↦ RationalVerdier.signedOppositeShift_naturality D l hl X
      (Coefficient.{u} l Ω L) K f n)
    (RationalVerdier.signedShift_evaluation D l hl X (Coefficient.{u} l Ω E)
      (F.omega E) (F.datum E) n)
    (RationalVerdier.signedShift_evaluation D l hl X (Coefficient.{u} l Ω L)
      (F.omega L) (F.datum L) n)
    (fun K P ↦ RationalVerdier.signedOppositeShift_scalar D l hl Ω X h n K P) K)

/-- Canonical finite internal-Hom shifts make the explicit components natural on
common-stage quotient arrows.
Source: blueprint thm-coef-qbar-verdier, proof steps 3--4, evaluation transpose and
finite-representative descent (blueprint: lem-coef-qbar-verdier-shift-naturality-K6).

Proof: use the signed reindexing of the internal Hom complex to define each finite
shift comparison. The tensor--Hom adjunction identifies it with the evaluation
transpose of the tensor shift comparison. The cone formula makes these the exact
finite Verdier shifts. A normalized scalar-extension beta preserves evaluation;
transposing its square shows that beta commutes with these chosen shifts. Represent
an arbitrary pair arrow over a common finite overfield. Finite naturality gives the
square there. The beta shift squares identify its two ends with the components at
the original source and target fields. Tower coherence makes this independent of
the representative. Hence the displayed naturality equation holds on the quotient.
Only this arrow equation is asserted here: zero and addition coherence and the
finite inclusion comparison are proved separately by categorical cancellation. -/
theorem finite_shift_naturality (F : Finite D l hl Ω X)
    (hF : FiniteCoherent D l hl Ω X F) :
    ∃ t : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
        (F.datum E).dual.CommShift ℤ,
      (∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
        letI := t E
        (F.datum E).dual.IsTriangulated) ∧
      ∀ (n : ℤ) (P Q : (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ)
        (f : P ⟶ Q),
        (descendedDual D l hl Ω X F hF).map (f⟦n⟧') ≫
          (shiftComponent D l hl Ω X F hF t n Q).hom =
        (shiftComponent D l hl Ω X F hF t n P).hom ≫
          ((descendedDual D l hl Ω X F hF).map f)⟦n⟧' := by
  let t := fun E : AlgebraicallyClosedCoefficients.Index l Ω ↦
    RationalVerdier.signedShift D l hl X (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)
      (F.omega E) (F.datum E)
  refine ⟨t, ?_, ?_⟩
  · intro E
    exact RationalVerdier.signedShift_exact D l hl X
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) (F.omega E) (F.datum E)
  · apply shiftComponent_naturality_of_beta D l hl Ω X F hF t
    intro E L h
    exact signedShift_stageComparison D l hl Ω X F h

end WeilConjectures.CoefQbarVerdier
