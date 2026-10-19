/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import Sheaf.AlgebraicGeometry.AbelianRepresentableGeneratorCoherence
import WeilConjectures.AlgebraicGeometry.ConstantSectionAdjunctPullback

/-! # Compatibility of the canonical comparison with smaller opens

Source: Stacks Project, Cohomology on Sites, Lemma 03F3.
(blueprint: lem-weil-pbc-etale-open-comparison-restriction).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private local instance restriction_isLeftAdjoint {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).IsLeftAdjoint :=
  (Etale.openImmersionRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j).isLeftAdjoint

-- Pointwise unit formulas, as in NestedOpenSectionUnit, proved here from the
-- public adjunction comparison API for the arbitrary immersions in this theorem.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise form of the restriction comparison unit equation.
-- Generalized to arbitrary coefficients from the abelian-group unit calculation.
open Opposite in
private theorem restriction_unit_coefficients
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {T Y : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology A)
    (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((Etale.upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
        ((Etale.upperStar A f).obj F).obj.map ψ.op ≫
        ((Etale.upperStarIsoLocalizationRestriction A f inferInstance).hom.app
          F).hom.app (op c) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv c b).symm ψ).op := by
  let ρ := (Etale.upperStarIsoLocalizationRestriction A f inferInstance).hom.app F
  have hu := congrArg (fun α ↦ α.hom.app (op b))
    (Adjunction.unit_leftAdjointUniq_hom_app (Etale.upperStarLowerStarAdjunction A f)
      (Etale.localizationRestrictionLowerStarAdjunction A f inferInstance) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  rw [ρ.hom.naturality, ← Category.assoc]
  erw [show ((Etale.upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
    ρ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj b)) =
    ((Etale.localizationRestrictionLowerStarAdjunction A f inferInstance).unit.app F).hom.app
      (op b) from hu]
  change (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise form of the composition unit equation, after restriction.
-- Generalized to arbitrary coefficients from the abelian-group unit calculation.
open Opposite in
private theorem composition_unit_coefficients
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {T Y R : Scheme.{u}}
    (f : T ⟶ Y) (g : Y ⟶ R) (t : T ⟶ R) (ht : t = f ≫ g)
    (F : Sheaf R.smallEtaleTopology A)
    (b : R.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b) :
    ((Etale.upperStarLowerStarAdjunction A t).unit.app F).hom.app (op b) ≫
        ((Etale.upperStar A t).obj F).obj.map ψ.op ≫
        ((Etale.upperStarComp A f g t ht).hom.app F).hom.app (op c) =
      ((Etale.upperStarLowerStarAdjunction A g).unit.app F).hom.app (op b) ≫
        ((Etale.upperStarLowerStarAdjunction A f).unit.app
          ((Etale.upperStar A g).obj F)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) ≫
        ((Etale.upperStar A f).obj
          ((Etale.upperStar A g).obj F)).obj.map
          (ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g t ht).hom.app
            b).op := by
  have h := congrArg (fun α ↦ α.hom.app (op b))
    (Etale.upperStarComp_hom_app_unit_app A f g F t ht)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, Etale.lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at h
  rw [((Etale.upperStarComp A f g t ht).hom.app F).hom.naturality, ← Category.assoc]
  erw [h]
  simp only [Functor.comp_obj, Iso.symm_inv, Etale.lowerStar_map_hom_app, Category.assoc,
    ← Functor.map_comp, ← op_comp]

-- The proof of nestedOpenSection_unit, with arbitrary presentations of the two opens.
-- Its site-level unit lemmas do not require the schemes to be literal open subschemes.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Opposite in
private theorem nestedImmersionSection_unit {X U V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) [IsOpenImmersion j] [IsOpenImmersion k]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let bU := Scheme.Etale.mk (𝟙 U)
    let bV := Scheme.Etale.mk (𝟙 V)
    let vU : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj bU
    let vV : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale (k ≫ j))).obj bV
    let f : vV ⟶ vU := MorphismProperty.Over.homMk k
      (by
        change k ≫ (𝟙 U ≫ j) = 𝟙 V ≫ (k ≫ j)
        simp only [Category.id_comp]) trivial
    let t : bV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ k).obj bU :=
      MorphismProperty.Over.homMk (pullback.lift k (𝟙 V)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp [bU, bV])
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      k).unit.app ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj F)).hom.app
        (op bU) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} k).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj F)).obj.map t.op ≫
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} k j (k ≫ j)
        rfl).inv.app F).hom.app (op bV) ≫
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} (k ≫ j)
        inferInstance).hom.app F).hom.app (op bV) =
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
        inferInstance).hom.app F).hom.app (op bU) ≫ F.obj.map f.op  := by
  dsimp only
  let A := AddCommGrpCat.{u + 1}
  let bU := Scheme.Etale.mk (𝟙 U)
  let bV := Scheme.Etale.mk (𝟙 V)
  let vU : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj bU
  let vV : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale (k ≫ j))).obj bV
  let f : vV ⟶ vU := MorphismProperty.Over.homMk k
    (by
      change k ≫ (𝟙 U ≫ j) = 𝟙 V ≫ (k ≫ j)
      simp only [Category.id_comp]) trivial
  let t : bV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ k).obj bU :=
    MorphismProperty.Over.homMk (pullback.lift k (𝟙 V)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp [bU, bV])
  let δ : bU ⟶ (MorphismProperty.Over.pullback @Etale ⊤ j).obj vU :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 U) (𝟙 U)
      (by
        change 𝟙 U ≫ (𝟙 U ≫ j) = 𝟙 U ≫ j
        simp only [Category.id_comp])) (by simp [bU])
  let ψ : bV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (k ≫ j)).obj vU :=
    MorphismProperty.Over.homMk (pullback.lift k (𝟙 V)
      (by
        change k ≫ (𝟙 U ≫ j) = 𝟙 V ≫ (k ≫ j)
        simp only [Category.id_comp])) (by simp [bV])
  let H := (Etale.upperStar A j).obj F
  let ρU := ((sheafSections _ A).obj (op bU)).mapIso
    ((Etale.upperStarIsoLocalizationRestriction A j inferInstance).app F)
  let ρV := ((sheafSections _ A).obj (op bV)).mapIso
    ((Etale.upperStarIsoLocalizationRestriction A (k ≫ j) inferInstance).app F)
  let C := ((sheafSections _ A).obj (op bV)).mapIso
    ((Etale.upperStarComp A k j (k ≫ j) rfl).app F)
  have hδ : ((Etale.upperStarLowerStarAdjunction A j).unit.app F).hom.app (op vU) ≫
      H.obj.map δ.op = ρU.inv := by
    have q := restriction_unit_coefficients A j F vU bU δ
    have hd : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance
        _root_.trivial).homEquiv bU vU).symm δ = 𝟙 vU := by
      ext
      simp [δ, Adjunction.homEquiv_counit]
      rfl
    rw [hd, op_id] at q
    erw [F.obj.map_id] at q
    exact (Iso.eq_comp_inv ρU).2 q
  have hψ : ((Etale.upperStarLowerStarAdjunction A (k ≫ j)).unit.app F).hom.app (op vU) ≫
      ((Etale.upperStar A (k ≫ j)).obj F).obj.map ψ.op ≫ ρV.hom = F.obj.map f.op := by
    have q := restriction_unit_coefficients A (k ≫ j) F vU bV ψ
    have hp : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ (k ≫ j) inferInstance
        _root_.trivial).homEquiv bV vU).symm ψ = f := by
      ext
      simp [ψ, f, Adjunction.homEquiv_counit]
    rw [hp] at q
    exact q
  have hχ : ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      k j (k ≫ j) rfl).hom.app vU =
      t ≫ (MorphismProperty.Over.pullback @Etale ⊤ k).map δ := by
    apply MorphismProperty.Over.Hom.ext
    change ψ.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      k j (k ≫ j) rfl).hom.app vU).left =
        t.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ k).map δ).left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
          Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
          limit.lift_π, PullbackCone.mk_π_app, Category.comp_id, limit.lift_π_assoc,
          cospan_left, vU, bU, ψ, t, δ]
        exact (Category.comp_id k).symm
      · simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
          Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
          limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app, Category.comp_id,
          limit.lift_π, cospan_left, vU, bU, ψ, t, δ]
        exact (Category.id_comp k).trans (Category.comp_id k).symm
    · simp [ψ, t, δ, bU, vU, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, Category.assoc]
  have hc := composition_unit_coefficients A k j (k ≫ j) rfl F vU bV ψ
  rw [hχ, op_comp, Functor.map_comp] at hc
  change _ = ((Etale.upperStarLowerStarAdjunction A j).unit.app F).hom.app (op vU) ≫
    ((Etale.upperStarLowerStarAdjunction A k).unit.app H).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ j).obj vU)) ≫
    ((Etale.lowerStar A k).obj ((Etale.upperStar A k).obj H)).obj.map δ.op ≫
    ((Etale.upperStar A k).obj H).obj.map t.op at hc
  erw [← ((Etale.upperStarLowerStarAdjunction A k).unit.app H).hom.naturality_assoc] at hc
  erw [reassoc_of% hδ] at hc
  have hc' : (ρU.inv ≫
      ((Etale.upperStarLowerStarAdjunction A k).unit.app H).hom.app (op bU) ≫
      ((Etale.upperStar A k).obj H).obj.map t.op) ≫ C.inv =
      ((Etale.upperStarLowerStarAdjunction A (k ≫ j)).unit.app F).hom.app (op vU) ≫
        ((Etale.upperStar A (k ≫ j)).obj F).obj.map ψ.op :=
    (Iso.comp_inv_eq C).2 hc.symm
  have q := congrArg (fun z ↦ ρU.hom ≫ z ≫ ρV.hom) hc'
  simp only [Category.assoc] at q
  erw [reassoc_of% ρU.hom_inv_id, hψ] at q
  exact q


open Opposite in
private theorem immersionSection_pullback {X U V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) [IsOpenImmersion j] [IsOpenImmersion k]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (m : (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} j).obj F) :
    let bU := Scheme.Etale.mk (𝟙 U)
    let bV := Scheme.Etale.mk (𝟙 V)
    let vU := (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj bU
    let vV := (MorphismProperty.Over.map ⊤ (inferInstance : Etale (k ≫ j))).obj bV
    let f : vV ⟶ vU := MorphismProperty.Over.homMk k
      (by
        change k ≫ (𝟙 U ≫ j) = 𝟙 V ≫ (k ≫ j)
        simp only [Category.id_comp]) trivial
    AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj V.smallEtaleTopology AddCommGrpCat.{u + 1}
        (show IsTerminal bV from IsTerminal.ofUniqueHom
          (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
          (fun a f ↦ by
            apply MorphismProperty.Over.Hom.ext
            exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))).homEquiv _ _
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          k).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
          (Etale.upperStar AddCommGrpCat.{u + 1} k).map m ≫
          (Etale.upperStarComp AddCommGrpCat.{u + 1} k j (k ≫ j)
            rfl).inv.app F)) =
      (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} (k ≫ j)
        inferInstance).inv.app F).hom.app (op bV))
        (F.obj.map f.op
          ((((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
            inferInstance).hom.app F).hom.app (op bU))
            (AddCommGrpCat.uliftZMultiplesAddEquiv _
              ((constantSheafAdj U.smallEtaleTopology AddCommGrpCat.{u + 1}
                (show IsTerminal bU from IsTerminal.ofUniqueHom
                  (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
                  (fun a f ↦ by
                    apply MorphismProperty.Over.Hom.ext
                    exact (Category.comp_id _).symm.trans
                      (MorphismProperty.Over.w f)))).homEquiv _ _ m)))) := by
  dsimp only
  simp only [← Category.assoc]
  rw [Adjunction.homEquiv_naturality_right]
  rw [constantSection_adjunct_pullback]
  have hz {B C : AddCommGrpCat.{u + 1}}
      (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ B) (g : B ⟶ C) :
      AddCommGrpCat.uliftZMultiplesAddEquiv C (f ≫ g) =
        g (AddCommGrpCat.uliftZMultiplesAddEquiv B f) := by rfl
  rw [hz, hz]
  have hn := nestedImmersionSection_unit j k F
  dsimp only at hn
  let e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} (k ≫ j)
    (inferInstance : Etale (k ≫ j))
  have hinv : (e.hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 V))) ≫
      (e.inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 V))) = 𝟙 _ := by
    exact (((sheafSections V.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk (𝟙 V)))).mapIso (e.app F)).hom_inv_id
  have hn' := congrArg
    (fun q ↦ q ≫ (e.inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 V)))) hn
  dsimp only [e] at hinv hn'
  simp only [Category.assoc, hinv, Category.comp_id] at hn'
  exact ConcreteCategory.congr_hom hn' _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
open Opposite in
private theorem restrictedSections_pullback {X U V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) [IsOpenImmersion j] [IsOpenImmersion k]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (m : EtaleOpenComparison.integerSheaf U ⟶
      (Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).obj G) :
    EtaleOpenComparison.restrictedSectionsEquiv (k ≫ j) G
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).inv.app
          (AddCommGrpCat.of (ULift ℤ)) ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} k).map m ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} k).map
          ((Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} j).inv.app G) ≫
        (Etale.upperStarComp AddCommGrpCat.{u + 1} k j).inv.app G ≫
        (Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1}
          (k ≫ j)).hom.app G) =
      G.obj.map
        (MorphismProperty.Over.homMk k rfl : Scheme.Etale.mk (k ≫ j) ⟶
          Scheme.Etale.mk j).op
        (EtaleOpenComparison.restrictedSectionsEquiv j G m) := by
  let bU := Scheme.Etale.mk (𝟙 U)
  let bV := Scheme.Etale.mk (𝟙 V)
  let vU : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj bU
  let vV : X.Etale :=
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale (k ≫ j))).obj bV
  let f : vV ⟶ vU := MorphismProperty.Over.homMk k
    (by
      change k ≫ (𝟙 U ≫ j) = 𝟙 V ≫ (k ≫ j)
      simp only [Category.id_comp]) trivial
  let ρU := Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} j
  let ρV := Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} (k ≫ j)
  let eU := ((constantSheafAdj U.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale U)).homAddEquiv _
      ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).obj G)).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  let eV := ((constantSheafAdj V.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @Etale V)).homAddEquiv _
      ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} (k ≫ j)).obj G)).trans
        (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  let p := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).inv.app
      (AddCommGrpCat.of (ULift ℤ)) ≫
    (Etale.upperStar AddCommGrpCat.{u + 1} k).map m ≫
    (Etale.upperStar AddCommGrpCat.{u + 1} k).map (ρU.inv.app G) ≫
    (Etale.upperStarComp AddCommGrpCat.{u + 1} k j).inv.app G ≫ ρV.hom.app G
  have h := immersionSection_pullback j k G (m ≫ ρU.inv.app G)
  dsimp only at h
  have hz {B C : AddCommGrpCat.{u + 1}}
      (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ B) (g : B ⟶ C) :
      AddCommGrpCat.uliftZMultiplesAddEquiv C (f ≫ g) =
        g (AddCommGrpCat.uliftZMultiplesAddEquiv B f) := by rfl
  have hraw : eV p = G.obj.map f.op (eU m) := by
    let eU' := ((constantSheafAdj U.smallEtaleTopology AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @Etale U)).homAddEquiv _
        ((Etale.upperStar AddCommGrpCat.{u + 1} j).obj G)).trans
          (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    let eV' := ((constantSheafAdj V.smallEtaleTopology AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @Etale V)).homAddEquiv _
        ((Etale.upperStar AddCommGrpCat.{u + 1} (k ≫ j)).obj G)).trans
          (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    let z := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).inv.app
        (AddCommGrpCat.of (ULift ℤ)) ≫
      (Etale.upperStar AddCommGrpCat.{u + 1} k).map (m ≫ ρU.inv.app G) ≫
      (Etale.upperStarComp AddCommGrpCat.{u + 1} k j).inv.app G
    change eV' z = ((ρV.inv.app G).hom.app (op bV))
      (G.obj.map f.op (((ρU.hom.app G).hom.app (op bU))
        (eU' (m ≫ ρU.inv.app G)))) at h
    have hm : eU' (m ≫ ρU.inv.app G) =
        ((ρU.inv.app G).hom.app (op bU)) (eU m) := by
      dsimp only [eU', eU, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
      rw [Adjunction.homEquiv_naturality_right, hz]
      rfl
    have hp : p = z ≫ ρV.hom.app G := by
      simp only [p, z, Functor.map_comp, Category.assoc]
    have he : eV p = ((ρV.hom.app G).hom.app (op bV)) (eV' z) := by
      rw [hp]
      dsimp only [eV, eV', AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
      rw [Adjunction.homEquiv_naturality_right, hz]
      rfl
    have hU := congrArg (fun z ↦ z.hom.app (op bU)) (ρU.inv_hom_id_app G)
    have hV := congrArg (fun z ↦ z.hom.app (op bV)) (ρV.inv_hom_id_app G)
    change _ ≫ _ = 𝟙 _ at hU hV
    have hU' : ((ρU.hom.app G).hom.app (op bU))
        (((ρU.inv.app G).hom.app (op bU)) (eU m)) = eU m :=
      ConcreteCategory.congr_hom hU (eU m)
    rw [he, h, hm, hU']
    exact ConcreteCategory.congr_hom hV (G.obj.map f.op (eU m))
  let iU : vU ≅ Scheme.Etale.mk j :=
    MorphismProperty.Over.isoMk (Iso.refl U) (Category.id_comp j)
  let iV : vV ≅ Scheme.Etale.mk (k ≫ j) :=
    MorphismProperty.Over.isoMk (Iso.refl V) (Category.id_comp (k ≫ j))
  let a : Scheme.Etale.mk (k ≫ j) ⟶ Scheme.Etale.mk j :=
    MorphismProperty.Over.homMk k rfl
  change G.obj.map iV.inv.op (eV p) = G.obj.map a.op (G.obj.map iU.inv.op (eU m))
  rw [hraw]
  have hi : iV.inv ≫ f = a ≫ iU.inv := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 V ≫ k = k ≫ 𝟙 U
    simp only [Category.id_comp, Category.comp_id]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hi,
    op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

open Opposite in
private theorem representingIso_hom_comp {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} j).obj
      (EtaleOpenComparison.integerSheaf U) ⟶ G) :
    (EtaleOpenComparison.representingIso j).hom ≫ f =
      EtaleOpenComparison.representingHomEquiv j G f := by
  change EtaleOpenComparison.representingHomEquiv j _ (𝟙 _) ≫ f = _
  simpa only [Category.id_comp] using
    (EtaleOpenComparison.representingHomEquiv_naturality j f (𝟙 _)).symm

open Opposite in
private theorem comparison_mk₀ {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (EtaleOpenComparison.freeSheaf X).obj (Scheme.Etale.mk j) ⟶ G) :
    etaleCohomologyOverOpenEquiv j G 0 (Abelian.Ext.mk₀ f) =
      Abelian.Ext.mk₀ ((EtaleOpenComparison.restrictedSectionsEquiv j G).symm
        (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G f)) := by
  let adj := Etale.openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j
  let g := (EtaleOpenComparison.restrictedSectionsEquiv j G).symm
    (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G f)
  apply (etaleCohomologyOverOpenEquiv j G 0).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change Abelian.Ext.mk₀ f =
    (Abelian.Ext.mk₀ (EtaleOpenComparison.representingIso j).hom).comp
      (adj.mapExtCounit (EtaleOpenComparison.integerSheaf U) G 0 (Abelian.Ext.mk₀ g))
      (zero_add 0)
  rw [Adjunction.mapExtCounit_mk₀, Abelian.Ext.mk₀_comp_mk₀, representingIso_hom_comp]
  congr 1
  apply (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk j) G).injective
  simp only [EtaleOpenComparison.representingHomEquiv, Equiv.trans_apply,
    AddEquiv.toEquiv_eq_coe, AddEquiv.coe_toEquiv]
  change _ = (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
    (Scheme.Etale.mk j) G) ((EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
      (Scheme.Etale.mk j) G).symm ((EtaleOpenComparison.restrictedSectionsEquiv j G)
        ((adj.homEquiv _ _) ((adj.homEquiv _ _).symm g))))
  rw [Equiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  exact (AddEquiv.apply_symm_apply _ _).symm

open Opposite in
private theorem comparison_connecting {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (n : ℕ)
    (y : Abelian.Ext ((EtaleOpenComparison.freeSheaf X).obj (Scheme.Etale.mk j)) S.X₃ n) :
    etaleCohomologyOverOpenEquiv j S.X₁ (n + 1) (y.comp hS.extClass rfl) =
      (etaleCohomologyOverOpenEquiv j S.X₃ n y).comp
        (hS.map_of_exact (Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j)).extClass
          rfl := by
  let R := Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j
  let L := Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} j
  have : R.IsLeftAdjoint :=
    (Etale.openImmersionRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j).isLeftAdjoint
  let adj := Etale.openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j
  let y' := etaleCohomologyOverOpenEquiv j S.X₃ n y
  have hy : (etaleCohomologyOverOpenEquiv j S.X₃ n).symm y' = y :=
    AddEquiv.symm_apply_apply _ y
  let φ : (S.map R).map L ⟶ S :=
    { τ₁ := adj.counit.app S.X₁
      τ₂ := adj.counit.app S.X₂
      τ₃ := adj.counit.app S.X₃
      comm₁₂ := (adj.counit.naturality S.f).symm
      comm₂₃ := (adj.counit.naturality S.g).symm }
  apply (etaleCohomologyOverOpenEquiv j S.X₁ (n + 1)).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change y.comp hS.extClass rfl =
    (Abelian.Ext.mk₀ (EtaleOpenComparison.representingIso j).hom).comp
      (adj.mapExtCounit (EtaleOpenComparison.integerSheaf U) S.X₁ (n + 1)
        (y'.comp (hS.map_of_exact R).extClass rfl)) (zero_add _)
  rw [Adjunction.mapExtCounit_apply,
    Adjunction.mapExactFunctor_comp_extClass_comp_mk₀ (hS.map_of_exact R) hS φ y']
  rw [← Abelian.Ext.comp_assoc]
  · exact congrArg (fun z ↦ z.comp hS.extClass rfl) hy.symm
  all_goals omega

open Opposite in
private theorem restriction_connecting {X U V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) [IsOpenImmersion j] [IsOpenImmersion k]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})]
    {S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact) (n : ℕ)
    (y : Sheaf.H ((Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j).obj S.X₃) n) :
    etaleCohomologyOverOpenRestriction j k S.X₁ (n + 1)
      (y.comp
        (hS.map_of_exact (Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j)).extClass
          rfl) =
      (etaleCohomologyOverOpenRestriction j k S.X₃ n y).comp
        (hS.map_of_exact
          (Etale.openImmersionRestriction AddCommGrpCat.{u + 1} (k ≫ j))).extClass rfl := by
  let R := Etale.openImmersionRestriction AddCommGrpCat.{u + 1} j
  let T := Etale.upperStar AddCommGrpCat.{u + 1} k
  let R' := Etale.openImmersionRestriction AddCommGrpCat.{u + 1} (k ≫ j)
  let ρ : R ⋙ T ≅ R' :=
    Functor.isoWhiskerRight
        (Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} j).symm T ≪≫
      (Etale.upperStarComp AddCommGrpCat.{u + 1} k j).symm ≪≫
      Etale.upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} (k ≫ j)
  let φ : (S.map R).map T ⟶ S.map R' :=
    { τ₁ := ρ.hom.app S.X₁
      τ₂ := ρ.hom.app S.X₂
      τ₃ := ρ.hom.app S.X₃
      comm₁₂ := (ρ.hom.naturality S.f).symm
      comm₂₃ := (ρ.hom.naturality S.g).symm }
  change ((Abelian.Ext.mk₀
    ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).inv.app
      (AddCommGrpCat.of (ULift ℤ)))).comp
        ((y.comp (hS.map_of_exact R).extClass rfl).mapExactFunctor T) (zero_add _)).comp
          (Abelian.Ext.mk₀ φ.τ₁) (add_zero _) = _
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Adjunction.mapExactFunctor_comp_extClass_comp_mk₀ (hS.map_of_exact R)
      (hS.map_of_exact R') φ y]
  rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)]
  rw [← Abelian.Ext.comp_assoc_of_third_deg_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical open-object comparison commutes with inclusion of a smaller open.
Both maps are specified independently: the left map is precomposition with the free
abelian sheaf map induced by k, and the right map is inverse-image cohomology pullback,
transported along the canonical inverse-image/restriction and composition isomorphisms.
Source: Stacks Project, Cohomology on Sites, Lemma 03F3 (2), and Sites, Section 00XZ.
(blueprint: lem-weil-pbc-etale-open-comparison-restriction).

Proof: resolve G by injective sheaves on X. Exact restriction along j and k preserves
injectives because its left adjoint is exact extension by zero. The representing
sections adjunction identifies Hom(A_j,I) with I(j) and Hom(A_{k≫j},I) with I(k≫j),
and sends precomposition with the free sheaf map of k to Ik. The constant-sheaf
adjunction identifies these same complexes with global sections of the restrictions
on U and V. Under these identifications, the inverse-image pullback on global sections
is also Ik: the units and the composition isomorphism of inverse image give exactly
restriction of sections. Thus the square commutes degreewise, hence on cohomology.
The exact Ext adjunction used in etaleCohomologyOverOpenEquiv is this comparison:
in degree zero it is the sections adjunction, and in higher degrees dimension shifting
along the same injective resolution gives the unique extension of that map. This proves
commutativity for the specified comparison, not for an arbitrarily chosen equivalence.
Identity inclusions, empty opens, zero coefficients, and degree zero need no exceptions. -/
theorem etaleCohomologyOverOpenEquiv_restriction {X U V : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ U) [IsOpenImmersion j] [IsOpenImmersion k]
    [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Abelian.Ext
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (uliftYoneda.{u + 1}.obj (Scheme.Etale.mk j) ⋙ AddCommGrpCat.free)) G q) :
    etaleCohomologyOverOpenEquiv (k ≫ j) G q
      ((Abelian.Ext.mk₀ ((EtaleOpenComparison.freeSheaf X).map
        (MorphismProperty.Over.homMk k rfl : Scheme.Etale.mk (k ≫ j) ⟶
          Scheme.Etale.mk j))).comp x (zero_add q)) =
      etaleCohomologyOverOpenRestriction j k G q
        (etaleCohomologyOverOpenEquiv j G q x) := by
  induction q generalizing G with
  | zero =>
    obtain ⟨f, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 x
    rw [Abelian.Ext.mk₀_comp_mk₀, comparison_mk₀, comparison_mk₀]
    simp only [etaleCohomologyOverOpenRestriction, AddMonoidHom.comp_apply,
      Etale.cohomologyMap_apply, Abelian.Ext.mapExactFunctor_mk₀,
      Sheaf.H.map_apply, Abelian.Ext.mk₀_comp_mk₀]
    congr 1
    apply (EtaleOpenComparison.restrictedSectionsEquiv (k ≫ j) G).injective
    rw [AddEquiv.apply_symm_apply]
    rw [Etale.sectionsEquiv_precomp]
    simpa only [AddEquiv.apply_symm_apply, Category.assoc, Iso.app_hom, Iso.symm_hom] using
      (restrictedSections_pullback j k G
        ((EtaleOpenComparison.restrictedSectionsEquiv j G).symm
          (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
            (Scheme.Etale.mk j) G f))).symm
  | succ n hn =>
    let I : InjectivePresentation G := Classical.arbitrary _
    have := I.injective
    let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    obtain ⟨y, rfl⟩ := Abelian.Ext.covariant_sequence_exact₁
      ((EtaleOpenComparison.freeSheaf X).obj (Scheme.Etale.mk j)) hS x
      (Abelian.Ext.eq_zero_of_injective (I := I.J) _) rfl
    rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)]
    rw [comparison_connecting (k ≫ j) hS n, comparison_connecting j hS n,
      restriction_connecting j k hS n, hn]

end AlgebraicGeometry
