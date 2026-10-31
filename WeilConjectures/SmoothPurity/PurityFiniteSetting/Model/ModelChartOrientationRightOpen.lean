/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelChartOrientationRestrictionDefinitions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelChartOrientationLeftOpen
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelOrientationPowerPullback
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs

/-! # Open naturality of the right orientation composite -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem iso_symm_app {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (q : F ≅ G) (X : C) : q.symm.app X = (q.app X).symm := by
  rfl

private theorem paste_tensor_isos {C : Type*} [Category C]
    {A B C₁ D E F G H I J K : C}
    {a : A ≅ B} {b : B ≅ C₁} {c : C₁ ≅ D} {d : D ≅ E} {e : E ≅ F}
    {t : B ≅ H} {u : H ≅ I} {v : I ≅ E} {p : A ≅ G} {q : G ≅ H}
    {r : I ≅ J} {s : J ≅ F} {x : G ≅ K} {y : K ≅ J}
    (hc : b ≪≫ c ≪≫ d = t ≪≫ u ≪≫ v)
    (ht : a ≪≫ t = p ≪≫ q) (hi : v ≪≫ e = r ≪≫ s)
    (hf : q ≪≫ u ≪≫ r = x ≪≫ y) :
    a ≪≫ b ≪≫ c ≪≫ d ≪≫ e = p ≪≫ x ≪≫ y ≪≫ s := by
  calc
    _ = a ≪≫ (b ≪≫ c ≪≫ d) ≪≫ e := by simp only [Iso.trans_assoc]
    _ = a ≪≫ (t ≪≫ u ≪≫ v) ≪≫ e := by rw [hc]
    _ = (a ≪≫ t) ≪≫ u ≪≫ (v ≪≫ e) := by simp only [Iso.trans_assoc]
    _ = (p ≪≫ q) ≪≫ u ≪≫ (r ≪≫ s) := by rw [ht, hi]
    _ = p ≪≫ (q ≪≫ u ≪≫ r) ≪≫ s := by simp only [Iso.trans_assoc]
    _ = p ≪≫ (x ≪≫ y) ≪≫ s := by rw [hf]
    _ = _ := by simp only [Iso.trans_assoc]

private theorem coefficientNoetherian (P : PurityFiniteSetting.{u}) :
    IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _

private theorem coefficientExponent (P : PurityFiniteSetting.{u}) :
    HasInvertibleExponent P.Coefficient (Spec (.of P.field.k)) :=
  P.comparedExponent (𝟙 (Spec (.of P.field.k)))

attribute [local instance] coefficientNoetherian coefficientExponent

private abbrev PD (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient))

private abbrev pull (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor

private theorem comparison_comp (P : PurityFiniteSetting.{u})
    {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R) (f : T ⟶ R) (h : f = a ≫ b)
    (K : Etale.DerivedCategoryModule P.Coefficient R) :
    Dnc.pullComparison P f K ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.mapIso
            ((Etale.leftDerivedUpperStarComp _ a b f h).app K) =
      (ProEtale.leftDerivedUpperStarCongr _ h).app _ ≪≫
        (ProEtale.leftDerivedUpperStarComp _ a b).app _ ≪≫
        (pull P a).mapIso (Dnc.pullComparison P b K) ≪≫
        Dnc.pullComparison P a
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.obj K) := by
  subst f
  apply Iso.ext
  simpa only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.trans_hom, Functor.mapIso_hom,
    Iso.refl_hom, Iso.app_hom, NatTrans.id_app, Category.id_comp, Category.assoc] using
      Dnc.pullComparison_comp P a b K

set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
private theorem comparison_square (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (j : X' ⟶ X) (v : Y' ⟶ Y) (h : j ≫ f = f' ≫ v)
    (M : Etale.DerivedCategoryModule P.Coefficient Y) :
    (pull P j).mapIso (Dnc.pullComparison P f M) ≪≫
        Dnc.pullComparison P j
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj M) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.mapIso
          ((Etale.leftDerivedUpperStarComp
              (ModuleCat.{u + 1} P.Coefficient) j f).symm.app M ≪≫
            (Etale.leftDerivedUpperStarComp
              (ModuleCat.{u + 1} P.Coefficient) f' v (j ≫ f) h).app M) =
      (ProEtale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) j f).symm.app _ ≪≫
        (ProEtale.leftDerivedUpperStarCongr
          (ModuleCat.{u + 1} P.Coefficient) h).app _ ≪≫
        (ProEtale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) f' v).app _ ≪≫
        (pull P f').mapIso (Dnc.pullComparison P v M) ≪≫
        Dnc.pullComparison P f'
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj M) := by
  have hj := congrArg Iso.hom (comparison_comp P j f (j ≫ f) rfl M)
  have hv := congrArg Iso.hom (comparison_comp P f' v (j ≫ f) h M)
  simp only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.trans_hom,
    Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Functor.mapIso_hom] at hj hv
  apply Iso.ext
  apply (cancel_epi ((ProEtale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) j f).hom.app _)).mp
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [← reassoc_of% hj]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using hv

private def tensorRestriction (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (j : X' ⟶ X) (v : Y' ⟶ Y) (h : j ≫ f = f' ≫ v)
    {K : PD P X} {L : PD P Y} {K' : PD P X'} {L' : PD P Y'}
    (c : (pull P j).obj K ≅ K') (b : (pull P v).obj L ≅ L') :=
  ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) j K
      ((pull P f).obj L) ≪≫
    P.compatibleTensorIso c
      ((ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) j f).symm.app L ≪≫
        (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) h).app L ≪≫
        (ProEtale.leftDerivedUpperStarComp
          (ModuleCat.{u + 1} P.Coefficient) f' v).app L ≪≫ (pull P f').mapIso b)

set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
private theorem tensorRestriction_naturality (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (j : X' ⟶ X) (v : Y' ⟶ Y) (h : j ≫ f = f' ≫ v)
    {K H : PD P X} {L M : PD P Y} {K' H' : PD P X'} {L' M' : PD P Y'}
    (a : K ≅ H) (b : L ≅ M) (a' : K' ≅ H') (b' : L' ≅ M')
    (c : (pull P j).obj K ≅ K') (q : (pull P v).obj L ≅ L')
    (r : (pull P j).obj H ≅ H') (s : (pull P v).obj M ≅ M')
    (ha : (pull P j).mapIso a ≪≫ r = c ≪≫ a')
    (hb : (pull P v).mapIso b ≪≫ s = q ≪≫ b') :
    (pull P j).mapIso (P.compatibleTensorIso a ((pull P f).mapIso b)) ≪≫
        tensorRestriction P f f' j v h r s =
      tensorRestriction P f f' j v h c q ≪≫
        P.compatibleTensorIso a' ((pull P f').mapIso b') := by
  let Q := (ProEtale.leftDerivedUpperStarComp
      (ModuleCat.{u + 1} P.Coefficient) j f).symm ≪≫
    ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) h ≪≫
      ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f' v
  have hn : (pull P j).mapIso ((pull P f).mapIso b) ≪≫ Q.app M ≪≫
        (pull P f').mapIso s =
      (Q.app L ≪≫ (pull P f').mapIso q) ≪≫ (pull P f').mapIso b' := by
    apply Iso.ext
    have he := congrArg Iso.hom hb
    simp only [Iso.trans_hom, Functor.mapIso_hom] at he
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
    erw [Q.hom.naturality_assoc]
    change Q.hom.app L ≫ (pull P f').map ((pull P v).map b.hom) ≫
        (pull P f').map s.hom = _
    rw [← CategoryTheory.Functor.map_comp, he, CategoryTheory.Functor.map_comp]
  have ht := compatibleTensorComparison_naturality
    (P.compatibleTensor X) (P.compatibleTensor X') (pull P j)
    (ProEtale.leftDerivedUpperStarTensorNatIso
      (ModuleCat.{u + 1} P.Coefficient) j) a ((pull P f).mapIso b)
  dsimp only [tensorRestriction]
  simp only [compatibleTensorIso, compatibleTensor,
    ProEtale.leftDerivedUpperStarTensorIso] at ht ⊢
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc, ht]
  simp only [Iso.trans_assoc]
  rw [compatibleBifunctorIso_trans, compatibleBifunctorIso_trans]
  simp only [Q, NatIso.trans_app, Iso.trans_assoc] at hn
  rw [ha, hn]
  simp only [Iso.trans_assoc]

private abbrev ED (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  Etale.DerivedCategoryModule P.Coefficient X

private abbrev compare (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory

private abbrev epull (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor

private def tensorLift (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : ED P X) (M : ED P Y) :=
  P.compatibleTensorIso (Iso.refl ((compare P X).obj K)) (Dnc.pullComparison P f M) ≪≫
    (compatibleComparisonTensor P.Coefficient X K ((epull P f).obj M)).symm

-- These constructions are used through their proved naturality equations below.
attribute [local irreducible] compatibleBifunctorIso compatibleComparisonTensor
  Dnc.pullComparison ProEtale.derivedTensor Etale.derivedTensor
  ProEtale.leftDerivedUpperStarTensorNatIso

set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
private theorem tensorLift_square (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (j : X' ⟶ X) (v : Y' ⟶ Y) (h : j ≫ f = f' ≫ v)
    (K : ED P X) (M : ED P Y) (K' : ED P X') (M' : ED P Y')
    (c : (epull P j).obj K ≅ K') (b : (epull P v).obj M ≅ M') :
    (pull P j).mapIso (tensorLift P f K M) ≪≫
        Dnc.pullComparison P j (((Etale.derivedTensor
          (ModuleCat.{u + 1} P.Coefficient) X).obj K).obj ((epull P f).obj M)) ≪≫
        (compare P X').mapIso
          (DiagonalPasting.tensorRestriction P.Coefficient P f f' j v h K M K' M' c b) =
      tensorRestriction P f f' j v h
        (Dnc.pullComparison P j K ≪≫ (compare P X').mapIso c)
        (Dnc.pullComparison P v M ≪≫ (compare P Y').mapIso b) ≪≫
          tensorLift P f' K' M' := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let G := epull P j
  let H := pull P j
  let F' := compare P X'
  let T := ProEtale.derivedTensor A X'
  let Qe := (Etale.leftDerivedUpperStarComp A j f).symm ≪≫
    Etale.leftDerivedUpperStarComp A f' v (j ≫ f) h
  let Qp := (ProEtale.leftDerivedUpperStarComp A j f).symm ≪≫
    ProEtale.leftDerivedUpperStarCongr A h ≪≫ ProEtale.leftDerivedUpperStarComp A f' v
  let b' := Qe.app M ≪≫ (epull P f').mapIso b
  have hb : H.mapIso (Dnc.pullComparison P f M) ≪≫
      Dnc.pullComparison P j ((epull P f).obj M) ≪≫ F'.mapIso b' =
    Qp.app ((compare P Y).obj M) ≪≫
      (pull P f').mapIso (Dnc.pullComparison P v M ≪≫ (compare P Y').mapIso b) ≪≫
      Dnc.pullComparison P f' M' := by
    have hs := comparison_square P f f' j v h M
    have hn := Dnc.pullComparison_naturality P f' b
    have hsh := congrArg Iso.hom hs
    have hnh := congrArg Iso.hom hn
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom] at hsh hnh
    apply Iso.ext
    simp only [b', Functor.mapIso_trans, Functor.mapIso_hom, Iso.trans_hom,
      Iso.app_hom, Category.assoc]
    simpa only [Qe, Qp, CategoryTheory.Functor.map_comp, Iso.trans_hom, Iso.app_hom,
      NatIso.trans_app, NatTrans.comp_app, A, H, F', pull, compare, epull,
      Category.assoc] using
      (Eq.trans (congrArg (fun z ↦ z ≫ F'.map ((epull P f').map b.hom)) hsh)
        (by
          simp only [Category.assoc]
          erw [← hnh]))
  have hc := comparisonTensorPullback P j K ((epull P f).obj M)
  have hn := compatibleTensorComparison_naturality
    (Etale.derivedTensor A X') T F' (ProEtale.comparisonTensorNatIso P.Coefficient X') c b'
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj] at hn
  rw [ProEtale.comparison_tensor_app, ProEtale.comparison_tensor_app] at hn
  have hi := compatibleIso_inverse_square _ _ _ _ hn
  have ht := compatibleTensorComparison_naturality
    (P.compatibleTensor X) T H (ProEtale.leftDerivedUpperStarTensorNatIso A j)
    (Iso.refl ((compare P X).obj K)) (Dnc.pullComparison P f M)
  have hfactors :
      compatibleBifunctorIso T
          (H.mapIso (Iso.refl ((compare P X).obj K)))
          (H.mapIso (Dnc.pullComparison P f M)) ≪≫
        compatibleBifunctorIso T (Dnc.pullComparison P j K)
          (Dnc.pullComparison P j ((epull P f).obj M)) ≪≫
        compatibleBifunctorIso T (F'.mapIso c) (F'.mapIso b') =
      P.compatibleTensorIso (B := X')
          (Dnc.pullComparison P j K ≪≫ F'.mapIso c)
          (Qp.app ((compare P Y).obj M) ≪≫
            (pull P f').mapIso (Dnc.pullComparison P v M ≪≫ (compare P Y').mapIso b)) ≪≫
        P.compatibleTensorIso (B := X') (Iso.refl ((compare P X').obj K'))
          (Dnc.pullComparison P f' M') := by
    simp only [compatibleTensorIso, compatibleTensor]
    simp only [← Iso.trans_assoc, compatibleBifunctorIso_trans]
    simp only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_assoc]
    rw [hb]
    erw [Iso.trans_refl]
  have hc0 : H.mapIso
        (compatibleComparisonTensor P.Coefficient X K ((epull P f).obj M)).symm ≪≫
      Dnc.pullComparison P j (((Etale.derivedTensor A X).obj K).obj ((epull P f).obj M)) ≪≫
      F'.mapIso (Etale.leftDerivedUpperStarTensorIso A j K ((epull P f).obj M)) =
    ProEtale.leftDerivedUpperStarTensorIso A j ((compare P X).obj K)
        ((compare P X).obj ((epull P f).obj M)) ≪≫
      compatibleBifunctorIso T (Dnc.pullComparison P j K)
        (Dnc.pullComparison P j ((epull P f).obj M)) ≪≫
      (compatibleComparisonTensor P.Coefficient X' (G.obj K)
        (G.obj ((epull P f).obj M))).symm := by
    simpa only [compatibleBifunctorIso, compatibleComparisonTensor,
      compatibleComparisonTensorGeneric, Iso.trans_assoc, Functor.comp_obj] using hc
  have hi0 : (compatibleComparisonTensor P.Coefficient X' (G.obj K)
        (G.obj ((epull P f).obj M))).symm ≪≫
        F'.mapIso (compatibleBifunctorIso (Etale.derivedTensor A X') c b') =
      compatibleBifunctorIso T (F'.mapIso c) (F'.mapIso b') ≪≫
        (compatibleComparisonTensor P.Coefficient X' K' ((epull P f').obj M')).symm := by
    simpa only [compatibleComparisonTensor, compatibleComparisonTensorGeneric,
      Functor.comp_obj, G] using hi
  have ht0 :
      H.mapIso (P.compatibleTensorIso (Iso.refl ((compare P X).obj K))
          (Dnc.pullComparison P f M)) ≪≫
        ProEtale.leftDerivedUpperStarTensorIso A j ((compare P X).obj K)
          ((compare P X).obj ((epull P f).obj M)) =
      ProEtale.leftDerivedUpperStarTensorIso A j ((compare P X).obj K)
          ((pull P f).obj ((compare P Y).obj M)) ≪≫
        compatibleBifunctorIso T (H.mapIso (Iso.refl ((compare P X).obj K)))
          (H.mapIso (Dnc.pullComparison P f M)) := by
    simpa only [compatibleTensorIso, compatibleTensor,
      ProEtale.leftDerivedUpperStarTensorIso] using ht
  have hz := paste_tensor_isos hc0 ht0 hi0 hfactors
  have hb' : b' =
      ((Etale.leftDerivedUpperStarComp A j f).app M).symm ≪≫
        (Etale.leftDerivedUpperStarComp A f' v (j ≫ f) h).app M ≪≫
          (epull P f').mapIso b := by
    simp only [b', Qe, NatIso.trans_app, iso_symm_app, Iso.trans_assoc]
  have hr :
      DiagonalPasting.tensorRestriction P.Coefficient P f f' j v h K M K' M' c b =
        Etale.leftDerivedUpperStarTensorIso A j K ((epull P f).obj M) ≪≫
          compatibleBifunctorIso (Etale.derivedTensor A X') c b' := by
    rw [hb']
    delta DiagonalPasting.tensorRestriction DiagonalPasting.tensorComparison
      compatibleBifunctorIso
    rfl
  rw [hr]
  unfold tensorLift tensorRestriction
  simpa only [Functor.mapIso_trans, Iso.trans_assoc, Qp, NatIso.trans_app,
    H, F', A, pull, compare, epull] using hz

set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
private theorem single_open (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine X'] [IsAffine Y']
    (r : ℕ) (h : X ⟶ Y) (h' : X' ⟶ Y') (j : X' ⟶ X) (v : Y' ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [SmoothOfRelativeDimension r h] [SmoothOfRelativeDimension r h']
    (w : j ≫ h = h' ≫ v)
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).leftDerivedFunctor.mapIso
        (P.chartDiagonalDelta r h aY ≪≫ P.chartDiagonalBeta r h aY t) ≪≫
      P.modelOrientationTwistPullback j (h ≫ aY) r =
    P.modelChartSectionRestriction r h h' j v w aY ≪≫
      P.chartDiagonalDelta r h' (v ≫ aY) ≪≫ P.chartDiagonalBeta r h' (v ≫ aY) t := by
  have transport (q : X ⟶ Y) (q' : X' ⟶ Y')
      [IsSeparated q] [LocallyOfFiniteType q] [QuasiCompact q]
      [IsSeparated q'] [LocallyOfFiniteType q'] [QuasiCompact q']
      [SmoothOfRelativeDimension r q] [SmoothOfRelativeDimension r q']
      (eq₁ : q = h ≫ 𝟙 Y) (eq₂ : q' = h' ≫ 𝟙 Y') (w' : j ≫ q = q' ≫ v) :
      (pull P j).mapIso (P.chartDiagonalDelta r q aY ≪≫
          P.chartDiagonalBeta r q aY t) ≪≫
        P.modelOrientationTwistPullback j (q ≫ aY) r =
      P.modelChartSectionRestriction r q q' j v w' aY ≪≫
        P.chartDiagonalDelta r q' (v ≫ aY) ≪≫ P.chartDiagonalBeta r q' (v ≫ aY) t := by
    subst q
    subst q'
    simpa only [modelChartLeft, Nat.add_zero, Category.assoc, Category.id_comp,
      Iso.trans_assoc] using
      P.model_chart_orientation_left_open r 0 h (𝟙 Y) h' (𝟙 Y') j v v w
        (by simp only [Category.comp_id, Category.id_comp]) aY t
  exact transport h h' (Category.comp_id h).symm (Category.comp_id h').symm w

private theorem single_orientation_congr (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (r : ℕ) (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension r f]
    (a b : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType a] [QuasiCompact a] [LocallyOfFiniteType b] [QuasiCompact b]
    (hab : a = b)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    (P.chartDiagonalDelta r f a ≪≫ P.chartDiagonalBeta r f a t) =
      (P.chartDiagonalDelta r f b ≪≫ P.chartDiagonalBeta r f b t) := by
  subst b
  rfl

set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
private theorem kappa_open (P : PurityFiniteSetting.{u})
    {U V T U' V' T' : Scheme.{u}}
    [IsAffine U] [IsAffine V] [IsAffine T]
    [IsAffine U'] [IsAffine V'] [IsAffine T']
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T) (f' : U' ⟶ V') (g' : V' ⟶ T')
    (j : U' ⟶ U) (v : V' ⟶ V) (w : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion v] [IsOpenImmersion w]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
    (hf : j ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w)
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT] :
    letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    letI := (DiagonalPasting.geometryProperties d e f' g').2.2.2.2
    (pull P j).mapIso (P.compatibleKappa d e f g aT) ≪≫
        P.modelChartSectionRestriction (d + e) (f ≫ g) (f' ≫ g') j w
          (DiagonalPasting.compositeSquare f g f' g' j v w hf hg) aT =
      tensorRestriction P f f' j v hf
        (P.modelChartSectionRestriction d f f' j v hf (g ≫ aT))
        (P.modelChartSectionRestriction e g g' v w hg aT) ≪≫
          P.compatibleKappa d e f' g' (w ≫ aT) := by
  let := P.noetherian aT
  let := P.noetherian (g ≫ aT)
  let := P.noetherian (f ≫ g ≫ aT)
  let := P.noetherian (w ≫ aT)
  let := P.noetherian (g' ≫ w ≫ aT)
  let := P.noetherian (f' ≫ g' ≫ w ≫ aT)
  let geom := DiagonalPasting.geometryProperties d e f g
  let := geom.1
  let := geom.2.1
  let := geom.2.2.1
  let := geom.2.2.2.1
  let := geom.2.2.2.2
  let geom' := DiagonalPasting.geometryProperties d e f' g'
  let := geom'.1
  let := geom'.2.1
  let := geom'.2.2.1
  let := geom'.2.2.2.1
  let := geom'.2.2.2.2
  let K := DiagonalPasting.diagonalSection P.Coefficient P f
  let M := DiagonalPasting.diagonalSection P.Coefficient P g
  let K' := DiagonalPasting.diagonalSection P.Coefficient P f'
  let M' := DiagonalPasting.diagonalSection P.Coefficient P g'
  let s1 := Dnc.sourceComparison P d (pullback.fst f f) (f ≫ g ≫ aT) (pullback.diagonal f)
  let s2 := Dnc.sourceComparison P e (pullback.fst g g) (g ≫ aT) (pullback.diagonal g)
  let s1' := Dnc.sourceComparison P d (pullback.fst f' f')
    (f' ≫ g' ≫ w ≫ aT) (pullback.diagonal f')
  let s2' := Dnc.sourceComparison P e (pullback.fst g' g')
    (g' ≫ w ≫ aT) (pullback.diagonal g')
  let S1 := DiagonalPasting.openSection P.Coefficient P d f f' j v hf (f ≫ g ≫ aT)
  let S2 := DiagonalPasting.openSection P.Coefficient P e g g' v w hg (g ≫ aT)
  let S3 := DiagonalPasting.openSection P.Coefficient P (d + e) (f ≫ g) (f' ≫ g') j w
    (DiagonalPasting.compositeSquare f g f' g' j v w hf hg) (f ≫ g ≫ aT)
  let r1 := P.modelChartSectionRestriction d f f' j v hf (g ≫ aT)
  let r2 := P.modelChartSectionRestriction e g g' v w hg aT
  have hs1 : (pull P j).mapIso s1 ≪≫ Dnc.pullComparison P j K ≪≫
      (compare P U').mapIso S1 = r1 ≪≫ s1' := by
    dsimp only [r1, s1, s1', K, S1, pull, compare]
    simp only [modelChartSectionRestriction, Iso.trans_assoc]
    erw [Iso.symm_self_id, Iso.trans_refl]
  have hs2 : (pull P v).mapIso s2 ≪≫ Dnc.pullComparison P v M ≪≫
      (compare P V').mapIso S2 = r2 ≪≫ s2' := by
    dsimp only [r2, s2, s2', M, S2, pull, compare]
    simp only [modelChartSectionRestriction, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  have hnatural := tensorRestriction_naturality P f f' j v hf s1 s2 s1' s2' r1 r2
    (Dnc.pullComparison P j K ≪≫ (compare P U').mapIso S1)
    (Dnc.pullComparison P v M ≪≫ (compare P V').mapIso S2) hs1 hs2
  have hlift := tensorLift_square P f f' j v hf K M K' M' S1 S2
  have he := ((DiagonalPasting.diagonalSectionPasting P d e f g aT).2
    f' g' j v w hf hg).1.2.2.2.2.1
  let k := DiagonalPasting.kappa P.Coefficient P d e f g aT
  let k' := DiagonalPasting.kappa P.Coefficient P d e f' g' (w ≫ aT)
  let S := DiagonalPasting.tensorRestriction P.Coefficient P f f' j v hf K M K' M' S1 S2
  let s3 := Dnc.sourceComparison P (d + e) (pullback.fst (f ≫ g) (f ≫ g))
    ((f ≫ g) ≫ aT) (pullback.diagonal (f ≫ g))
  let s3' := Dnc.sourceComparison P (d + e) (pullback.fst (f' ≫ g') (f' ≫ g'))
    ((f' ≫ g') ≫ w ≫ aT) (pullback.diagonal (f' ≫ g'))
  let I := P.compatibleTensorIso s1 ((pull P f).mapIso s2) ≪≫ tensorLift P f K M
  let I' := P.compatibleTensorIso s1' ((pull P f').mapIso s2') ≪≫ tensorLift P f' K' M'
  let R := tensorRestriction P f f' j v hf r1 r2
  have hI : (pull P j).mapIso I ≪≫
      Dnc.pullComparison P j (((Etale.derivedTensor
        (ModuleCat.{u + 1} P.Coefficient) U).obj K).obj ((epull P f).obj M)) ≪≫
      (compare P U').mapIso S = R ≪≫ I' := by
    simp only [I, I', Functor.mapIso_trans, Iso.trans_assoc]
    rw [hlift]
    rw [← Iso.trans_assoc, hnatural]
    simp only [R, Iso.trans_assoc]
  have heI : (compare P U').mapIso ((epull P j).mapIso k ≪≫ S3) =
      (compare P U').mapIso (S ≪≫ k') := by
    apply Iso.ext
    simpa only [k, k', S, S1, S2, S3, compare, epull,
      DiagonalPasting.SameProEtaleMap, Iso.trans_hom,
      Functor.mapIso_hom, CategoryTheory.Functor.map_comp] using he
  have hn := Dnc.pullComparison_naturality P j k
  have hIk : (pull P j).mapIso (I ≪≫ (compare P U).mapIso k) ≪≫
        Dnc.pullComparison P j (DiagonalPasting.diagonalSection P.Coefficient P (f ≫ g)) ≪≫
        (compare P U').mapIso S3 = R ≪≫ I' ≪≫ (compare P U').mapIso k' := by
    simp only [Functor.mapIso_trans, Iso.trans_assoc]
    rw [← Iso.trans_assoc ((pull P j).mapIso ((compare P U).mapIso k)), hn]
    simp only [Iso.trans_assoc]
    rw [← Functor.mapIso_trans, heI, Functor.mapIso_trans]
    have hIh := congrArg Iso.hom hI
    apply Iso.ext
    simpa only [I, Functor.mapIso_trans, Iso.trans_hom, Functor.mapIso_hom,
      CategoryTheory.Functor.map_comp, Category.assoc] using
      congrArg (fun z ↦ z ≫ ((compare P U').mapIso k').hom) hIh
  have hk : I ≪≫ (compare P U).mapIso k ≪≫ s3.symm =
      P.compatibleKappa d e f g aT := by
    simp only [I, tensorLift, compatibleKappa, compatibleTensorIso,
      ← Iso.trans_assoc, compatibleBifunctorIso_trans]
    simp only [s1, s2, K, M, compare, Dnc.sourceEtale,
      DiagonalPasting.diagonalSection, Iso.trans_assoc, Iso.trans_refl]
    rfl
  have hk' : I' ≪≫ (compare P U').mapIso k' ≪≫ s3'.symm =
      P.compatibleKappa d e f' g' (w ≫ aT) := by
    simp only [I', tensorLift, compatibleKappa, compatibleTensorIso,
      ← Iso.trans_assoc, compatibleBifunctorIso_trans]
    simp only [s1', s2', K', M', compare, Dnc.sourceEtale,
      DiagonalPasting.diagonalSection, Iso.trans_assoc, Iso.trans_refl]
    rfl
  rw [← hk, ← hk']
  change (pull P j).mapIso (I ≪≫ (compare P U).mapIso k ≪≫ s3.symm) ≪≫
      ((pull P j).mapIso s3 ≪≫ Dnc.pullComparison P j _ ≪≫
        (compare P U').mapIso S3 ≪≫ s3'.symm) =
    R ≪≫ I' ≪≫ (compare P U').mapIso k' ≪≫ s3'.symm
  simp only [Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc,
    Iso.symm_self_id_assoc]
  simpa only [Functor.mapIso_trans, Iso.trans_assoc,
    Dnc.sourceEtale, DiagonalPasting.diagonalSection] using
    congrArg (fun z ↦ z ≪≫ s3'.symm) hIk

set_option maxHeartbeats 2000000 in
-- The comparison calculation elaborates large derived-category expressions.
/-- Open naturality of the tensor orientation on the common total section source.
Source: model descent Steps 8--9; diagonal section pasting open naturality and
canonical tensor and Tate pullback coherence.
(blueprint: lem-pur-model-chart-orientation-right-open).

Proof: expand modelChartRight as inverse kappa, tensor of the two delta-beta
orientations, and mu. The open kappa square in diagonalSectionPastingOpen
restricts its inverse through the canonical tensor source comparison and the
total open-section comparison. For the first orientation use source-open
restriction after target-open base change. For the second use the same square
on V', followed by pullback along f'. The commuting square hf and the pullback
compositor identify this with restriction along j of the original pulled-back
second orientation. Normalized DNC restriction and integration-normalized
normal-bundle restriction give these two orientation squares. Naturality of
the derived tensor pullback constraint tensors the squares. The Tate pullback
cocycle and compatibility of ordered tensor-power multiplication with pullback
identify the resulting target comparison with the total Tate pullback in the
statement. The intermediate tensor source comparisons cancel against the
inverse-kappa square, leaving modelChartSectionRestriction as the sole source
comparison. All maps retain their given order; no symmetry or choice of frames
is introduced. The same tensor-unit and empty-cover equations include rank
zero and empty opens. -/
theorem model_chart_orientation_right_open (P : PurityFiniteSetting.{u})
    {U V T U' V' T' : Scheme.{u}}
    [IsAffine U] [IsAffine V] [IsAffine T]
    [IsAffine U'] [IsAffine V'] [IsAffine T']
    (d e : ℕ) (f : U ⟶ V) (g : V ⟶ T) (f' : U' ⟶ V') (g' : V' ⟶ T')
    (j : U' ⟶ U) (v : V' ⟶ V) (w : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion v] [IsOpenImmersion w]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    [SmoothOfRelativeDimension d f'] [SmoothOfRelativeDimension e g']
    (hf : j ≫ f = f' ≫ v) (hg : v ≫ g = g' ≫ w)
    (aT : T ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
    letI := (DiagonalPasting.geometryProperties d e f' g').2.2.2.2
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).leftDerivedFunctor.mapIso
        (P.modelChartRight d e f g aT t) ≪≫
      P.modelOrientationTwistPullback j (f ≫ g ≫ aT) (d + e) =
    P.modelChartSectionRestriction (d + e) (f ≫ g) (f' ≫ g') j w
        (DiagonalPasting.compositeSquare f g f' g' j v w hf hg) aT ≪≫
      P.modelChartRight d e f' g' (w ≫ aT) t := by
  let := (DiagonalPasting.geometryProperties d e f g).2.2.2.2
  let := (DiagonalPasting.geometryProperties d e f' g').2.2.2.2
  have hvg : v ≫ g ≫ aT = g' ≫ w ≫ aT := by
    rw [← Category.assoc, hg, Category.assoc]
  let a := P.chartDiagonalDelta d f (g ≫ aT) ≪≫ P.chartDiagonalBeta d f (g ≫ aT) t
  let b := P.chartDiagonalDelta e g aT ≪≫ P.chartDiagonalBeta e g aT t
  let a' := P.chartDiagonalDelta d f' (g' ≫ w ≫ aT) ≪≫
    P.chartDiagonalBeta d f' (g' ≫ w ≫ aT) t
  let b' := P.chartDiagonalDelta e g' (w ≫ aT) ≪≫
    P.chartDiagonalBeta e g' (w ≫ aT) t
  let c := P.modelChartSectionRestriction d f f' j v hf (g ≫ aT)
  let q := P.modelChartSectionRestriction e g g' v w hg aT
  let r := P.modelOrientationTwistPullback j (f ≫ g ≫ aT) d
  let s := P.modelOrientationTwistPullback v (g ≫ aT) e
  have ha : (pull P j).mapIso a ≪≫ r = c ≪≫ a' := by
    have hh := single_open P d f f' j v hf (g ≫ aT) t
    have hc := single_orientation_congr P d f' (v ≫ g ≫ aT) (g' ≫ w ≫ aT) hvg t
    simpa only [a, a', c, r, Iso.trans_assoc] using
      hh.trans (congrArg (fun z ↦ c ≪≫ z) hc)
  have hb : (pull P v).mapIso b ≪≫ s = q ≪≫ b' := by
    simpa only [b, b', q, s, Iso.trans_assoc] using
      single_open P e g g' v w hg aT t
  have hn := tensorRestriction_naturality P f f' j v hf a b a' b' c q r s ha hb
  have hm : (pull P j).mapIso (P.modelOrientationMu d e f (g ≫ aT)) ≪≫
        P.modelOrientationTwistPullback j (f ≫ g ≫ aT) (d + e) =
      tensorRestriction P f f' j v hf r s ≪≫
        P.modelOrientationMu d e f' (g' ≫ w ≫ aT) := by
    simpa only [tensorRestriction, r, s, Category.assoc, hvg,
      Iso.trans_assoc, diagonalTwist, pull] using
      modelOrientationMu_pullback P d e f f' j v hf (g ≫ aT)
  have hk := kappa_open P d e f g f' g' j v w hf hg aT
  have hki := compatibleIso_inverse_square _ _ _ _ hk.symm
  have hnh := congrArg Iso.hom hn
  have hmh := congrArg Iso.hom hm
  have hkh := congrArg Iso.hom hki
  simp only [a, b, a', b', c, q, r, s, pull, Iso.trans_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom] at hnh hmh hkh
  apply Iso.ext
  simp only [modelChartRight, Iso.trans_hom, Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, Iso.symm_hom, Category.assoc]
  rw [hmh, reassoc_of% hnh, reassoc_of% hkh]

end WeilConjectures.PurityFiniteSetting
