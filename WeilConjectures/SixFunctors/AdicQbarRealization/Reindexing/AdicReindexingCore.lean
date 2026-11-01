/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import WeilConjectures.SixFunctors.AdicQbarRealization.AdicCoefficientRingReindexing
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralReindexingDescent
import WeilConjectures.SixFunctors.AdicQbarRealization.Tensor.AdicTensorReindexingModels
import WeilConjectures.SixFunctors.AdicQbarRealization.AdicCommonPullbackIdentityUnit
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorIso

/-! # Normalized integral and common-stage reindexing

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

private theorem inverse_functions {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {R : LocallyFiniteAdicRealization.Realization l X}
    {S : LocallyFiniteAdicRealization.Realization l Y} (B : RingReindex l X g R S)
    (W : X.ProEtᵒᵖ) (s : (ring l X R).obj.obj W) (x : W.unop.left) :
    (B.iso.inv.hom.app W s).down.1 x = s.down.1 x := by
  have h := B.functions W (B.iso.inv.hom.app W s) x
  have hcancel := congrArg (fun f ↦ (f.hom.app W s).down.1 x) B.iso.inv_hom_id
  exact h.symm.trans hcancel

set_option backward.isDefEq.respectTransparency true

private theorem coefficientIdEq (T : GeometricSpace D)
    (R : LocallyFiniteAdicRealization.Realization l T.base.left)
    (B : RingReindex l T.base.left (𝟙 _) R R) :
    let e : proEtaleIsoPostcompose (𝟙 T.base.left) ≅ 𝟭 T.base.left.ProEt :=
      MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤)
        T.base.left (𝟙 _) rfl
    let RR := (sheafCompose (ProEt.topology T.base.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l T.base.left R)
    let c := inv (((sheafCompose (ProEt.topology T.base.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso).hom)
    𝟙 RR ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom
      RingCat.{u + 1} (ProEt.topology T.base.left) (ProEt.topology T.base.left)).app RR = c := by
  dsimp only
  ext W s
  apply ULift.ext
  apply Subtype.ext
  ext x
  rw [IsIso.Iso.inv_hom]
  change s.down.1 x = (B.iso.inv.hom.app W s).down.1 x
  exact (inverse_functions l _ B W s x).symm

private theorem coefficientCompEq (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (R : LocallyFiniteAdicRealization.Realization l T.base.left)
    (S : LocallyFiniteAdicRealization.Realization l U.base.left)
    (P : LocallyFiniteAdicRealization.Realization l V.base.left)
    (B : RingReindex l T.base.left (g ≪≫ h).hom R P)
    (Bg : RingReindex l T.base.left g.hom R S)
    (Bh : RingReindex l U.base.left h.hom S P) :
    let RR := (sheafCompose (ProEt.topology T.base.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l T.base.left R)
    let _SS := (sheafCompose (ProEt.topology U.base.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l U.base.left S)
    let PP := (sheafCompose (ProEt.topology V.base.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l V.base.left P)
    let F := proEtaleIsoPostcompose g.hom
    let G := proEtaleIsoPostcompose h.hom
    let e : proEtaleIsoPostcompose (g ≪≫ h).hom ≅ F ⋙ G :=
      MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale g.hom) (inferInstance : WeaklyEtale h.hom)
    letI compContinuous : (F ⋙ G).IsContinuous (ProEt.topology T.base.left)
        (ProEt.topology V.base.left) := Functor.isContinuous_comp F G (ProEt.topology T.base.left)
      (ProEt.topology U.base.left) (ProEt.topology V.base.left)
    let c := inv (((sheafCompose (ProEt.topology T.base.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso).hom)
    let cg := inv (((sheafCompose (ProEt.topology T.base.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso Bg.iso).hom)
    let ch := inv (((sheafCompose (ProEt.topology U.base.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso Bh.iso).hom)
    let cc : RR ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology T.base.left) (ProEt.topology V.base.left)).obj PP :=
      cg ≫ (F.sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology T.base.left) (ProEt.topology U.base.left)).map ch
    cc ≫ (Functor.sheafPushforwardContinuousNatTrans
      (F := proEtaleIsoPostcompose (g ≪≫ h).hom)
      (F' := F ⋙ G) e.hom RingCat.{u + 1}
      (ProEt.topology T.base.left) (ProEt.topology V.base.left)).app PP = c := by
  dsimp only
  ext W s
  apply ULift.ext
  apply Subtype.ext
  ext x
  simp only [IsIso.Iso.inv_hom]
  change (Bh.iso.inv.hom.app ((proEtaleIsoPostcompose g.hom).op.obj W)
      (Bg.iso.inv.hom.app W s)).down.1 x = (B.iso.inv.hom.app W s).down.1 x
  rw [inverse_functions, inverse_functions, inverse_functions]

private def pushforwardIdentity
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (F : C ⥤ C) [F.IsContinuous J J]
    (R : Sheaf J RingCat.{u + 1}) (e : F ≅ 𝟭 C)
    (c : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J J).obj R)
    (hc : 𝟙 R ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom
      RingCat.{u + 1} J J).app R = c) :
    SheafOfModules.pushforward.{u + 1} (F := F) c ≅ 𝟭 (SheafOfModules.{u + 1} R) :=
  (SheafOfModules.pushforwardCongr₂.{u + 1} (F := F) (G := 𝟭 C)
    (T := R) (S := R) (ψ := c) (𝟙 R) e hc).symm ≪≫
      SheafOfModules.pushforwardId.{u + 1} R

private def pushforwardComposition
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.IsContinuous J K] [G.IsContinuous K L] [H.IsContinuous J L]
    [(F ⋙ G).IsContinuous J L]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (T : Sheaf L RingCat.{u + 1}) (e : H ≅ F ⋙ G)
    (cg : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S)
    (ch : S ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} K L).obj T)
    (c : R ⟶ (H.sheafPushforwardContinuous RingCat.{u + 1} J L).obj T)
    (hc : (cg ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map ch) ≫
      (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u + 1} J L).app T = c) :
    SheafOfModules.pushforward.{u + 1} (F := H) c ≅
      SheafOfModules.pushforward.{u + 1} (F := G) ch ⋙
        SheafOfModules.pushforward.{u + 1} (F := F) cg :=
  (SheafOfModules.pushforwardCongr₂.{u + 1} (F := H) (G := F ⋙ G)
    (T := R) (S := T) (ψ := c)
    (cg ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map ch) e hc).symm ≪≫
      (SheafOfModules.pushforwardComp (F := F) (G := G) cg ch).symm

private theorem pushforwardIdentity_sections
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (F : C ⥤ C) [F.IsContinuous J J]
    (R : Sheaf J RingCat.{u + 1}) (e : F ≅ 𝟭 C)
    (c : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J J).obj R)
    (hc : 𝟙 R ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom
      RingCat.{u + 1} J J).app R = c)
    (M : SheafOfModules.{u + 1} R) (U : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{u + 1} (F := F) c).obj M).val.obj U) :
    (((pushforwardIdentity J F R e c hc).hom.app M).val.app U x) =
      M.val.map (e.inv.app U.unop).op x := rfl

private theorem pushforwardComposition_sections
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E) (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.IsContinuous J K] [G.IsContinuous K L] [H.IsContinuous J L]
    [(F ⋙ G).IsContinuous J L]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (T : Sheaf L RingCat.{u + 1}) (e : H ≅ F ⋙ G)
    (cg : R ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S)
    (ch : S ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} K L).obj T)
    (c : R ⟶ (H.sheafPushforwardContinuous RingCat.{u + 1} J L).obj T)
    (hc : (cg ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map ch) ≫
      (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u + 1} J L).app T = c)
    (M : SheafOfModules.{u + 1} T) (U : Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{u + 1} (F := H) c).obj M).val.obj U) :
    (((pushforwardComposition J K L F G H R S T e cg ch c hc).hom.app M).val.app U x) =
      M.val.map (e.inv.app U.unop).op x := rfl

private instance weaklyEtaleComp :
    MorphismProperty.IsStableUnderComposition (@WeaklyEtale.{u}) := by infer_instance

set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] LocallyFiniteAdicRealization.ringSheaf

private def normalizedModuleId (T : GeometricSpace D)
    (R : LocallyFiniteAdicRealization.Realization l T.base.left)
    (B : RingReindex l T.base.left (𝟙 _) R R) :
    modulePull l T.base.left (𝟙 _) B ≅ 𝟭 (modules l T.base.left R) := by
  dsimp only [modulePull, isoSectionwiseModuleInverseImage]
  let e : proEtaleIsoPostcompose (𝟙 T.base.left) ≅ 𝟭 T.base.left.ProEt :=
    MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤)
      T.base.left (𝟙 _) rfl
  let RR := (sheafCompose (ProEt.topology T.base.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l T.base.left R)
  let c := inv (((sheafCompose (ProEt.topology T.base.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso).hom)
  have he : 𝟙 RR ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom
      RingCat.{u + 1} (ProEt.topology T.base.left) (ProEt.topology T.base.left)).app RR = c :=
    coefficientIdEq l D T R B
  exact pushforwardIdentity (ProEt.topology T.base.left)
    (proEtaleIsoPostcompose (𝟙 T.base.left)) RR e c he

private def normalizedModuleComp (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (R : LocallyFiniteAdicRealization.Realization l T.base.left)
    (S : LocallyFiniteAdicRealization.Realization l U.base.left)
    (P : LocallyFiniteAdicRealization.Realization l V.base.left)
    (B : RingReindex l T.base.left (g ≪≫ h).hom R P)
    (Bg : RingReindex l T.base.left g.hom R S)
    (Bh : RingReindex l U.base.left h.hom S P) :
    modulePull l T.base.left (g ≪≫ h).hom B ≅
      modulePull l U.base.left h.hom Bh ⋙ modulePull l T.base.left g.hom Bg := by
  dsimp only [modulePull, isoSectionwiseModuleInverseImage]
  let RR := (sheafCompose (ProEt.topology T.base.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l T.base.left R)
  let _SS := (sheafCompose (ProEt.topology U.base.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l U.base.left S)
  let PP := (sheafCompose (ProEt.topology V.base.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l V.base.left P)
  let F := proEtaleIsoPostcompose g.hom
  let G := proEtaleIsoPostcompose h.hom
  let e : proEtaleIsoPostcompose (g ≪≫ h).hom ≅ F ⋙ G :=
    MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale g.hom) (inferInstance : WeaklyEtale h.hom)
  letI compContinuous : (F ⋙ G).IsContinuous (ProEt.topology T.base.left)
      (ProEt.topology V.base.left) := Functor.isContinuous_comp F G (ProEt.topology T.base.left)
    (ProEt.topology U.base.left) (ProEt.topology V.base.left)
  let c := inv (((sheafCompose (ProEt.topology T.base.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso).hom)
  let cg := inv (((sheafCompose (ProEt.topology T.base.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso Bg.iso).hom)
  let ch := inv (((sheafCompose (ProEt.topology U.base.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso Bh.iso).hom)
  let cc : RR ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology T.base.left) (ProEt.topology V.base.left)).obj PP :=
    cg ≫ (F.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology T.base.left) (ProEt.topology U.base.left)).map ch
  have he : cc ≫ (Functor.sheafPushforwardContinuousNatTrans
      (F := proEtaleIsoPostcompose (g ≪≫ h).hom)
      (F' := F ⋙ G) e.hom RingCat.{u + 1}
      (ProEt.topology T.base.left) (ProEt.topology V.base.left)).app PP = c :=
    coefficientCompEq l D T U V g h R S P B Bg Bh
  exact pushforwardComposition (ProEt.topology T.base.left) (ProEt.topology U.base.left)
    (ProEt.topology V.base.left) F G (proEtaleIsoPostcompose (g ≪≫ h).hom)
    RR _SS PP e cg ch c he

private theorem restrictionApply
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u + 1}}
    (M : PresheafOfModules.{u + 1} R) {U V : C} (h : U = V)
    (x : M.obj (Opposite.op V)) : HEq (M.map (eqToHom h).op x) x := by
  subst V
  rw [eqToHom_refl, op_id, M.map_id]
  exact HEq.rfl

private theorem normalizedModuleId_sections (T : GeometricSpace D)
    (R : LocallyFiniteAdicRealization.Realization l T.base.left)
    (B : RingReindex l T.base.left (𝟙 _) R R)
    (M : modules l T.base.left R) (U : T.base.left.ProEtᵒᵖ)
    (x : ((modulePull l T.base.left (𝟙 _) B).obj M).val.obj U) :
    HEq (((normalizedModuleId l D T R B).hom.app M).val.app U x) x := by
  let e : proEtaleIsoPostcompose (𝟙 T.base.left) ≅ 𝟭 T.base.left.ProEt :=
    MorphismProperty.Over.mapId (P := @WeaklyEtale) (Q := ⊤)
      T.base.left (𝟙 _) rfl
  dsimp only [normalizedModuleId, id]
  erw [pushforwardIdentity_sections]
  change HEq (M.val.map (e.inv.app U.unop).op x) x
  have hsite : (proEtaleIsoPostcompose (𝟙 T.base.left)).obj U.unop = U.unop := by
    rcases U with ⟨⟨⟨A, B, f⟩, hf⟩⟩
    change (⟨⟨A, B, f ≫ 𝟙 _⟩, _⟩ : T.base.left.ProEt) = ⟨⟨A, B, f⟩, hf⟩
    simp only [Category.comp_id]
  let L : T.base.left.ProEt ⥤ Scheme.{u} :=
    MorphismProperty.Over.forget @WeaklyEtale ⊤ T.base.left ⋙
      CategoryTheory.Over.forget T.base.left
  have he : e.inv.app U.unop = eqToHom hsite.symm := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 U.unop.left = L.map (eqToHom hsite.symm)
    have h := (eqToHom_map L hsite.symm).symm
    change eqToHom (rfl : U.unop.left = U.unop.left) = L.map (eqToHom hsite.symm) at h
    exact h
  rw [he]
  exact restrictionApply M.val hsite.symm x

private theorem normalizedModuleComp_sections (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (R : LocallyFiniteAdicRealization.Realization l T.base.left)
    (S : LocallyFiniteAdicRealization.Realization l U.base.left)
    (P : LocallyFiniteAdicRealization.Realization l V.base.left)
    (B : RingReindex l T.base.left (g ≪≫ h).hom R P)
    (Bg : RingReindex l T.base.left g.hom R S)
    (Bh : RingReindex l U.base.left h.hom S P)
    (M : modules l V.base.left P) (W : T.base.left.ProEtᵒᵖ)
    (x : ((modulePull l T.base.left (g ≪≫ h).hom B).obj M).val.obj W) :
    HEq (((normalizedModuleComp l D T U V g h R S P B Bg Bh).hom.app M).val.app W x) x := by
  let e : proEtaleIsoPostcompose (g ≪≫ h).hom ≅
      proEtaleIsoPostcompose g.hom ⋙ proEtaleIsoPostcompose h.hom :=
    MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale g.hom) (inferInstance : WeaklyEtale h.hom)
  dsimp only [normalizedModuleComp, id]
  erw [pushforwardComposition_sections]
  change HEq (M.val.map (e.inv.app W.unop).op x) x
  have hsite : (proEtaleIsoPostcompose (g ≪≫ h).hom).obj W.unop =
      (proEtaleIsoPostcompose h.hom).obj ((proEtaleIsoPostcompose g.hom).obj W.unop) := by
    rcases W with ⟨⟨⟨A, B, f⟩, hf⟩⟩
    change (⟨⟨A, B, f ≫ (g.hom ≫ h.hom)⟩, _⟩ : V.base.left.ProEt) =
      ⟨⟨A, B, (f ≫ g.hom) ≫ h.hom⟩, _⟩
    simp only [Category.assoc]
  let L : V.base.left.ProEt ⥤ Scheme.{u} :=
    MorphismProperty.Over.forget @WeaklyEtale ⊤ V.base.left ⋙
      CategoryTheory.Over.forget V.base.left
  have he : e.inv.app W.unop = eqToHom hsite.symm := by
    apply MorphismProperty.Over.Hom.ext
    change 𝟙 W.unop.left = L.map (eqToHom hsite.symm)
    have h := (eqToHom_map L hsite.symm).symm
    change eqToHom (rfl : W.unop.left = W.unop.left) = L.map (eqToHom hsite.symm) at h
    exact h
  rw [he]
  exact restrictionApply M.val hsite.symm x

private theorem sourceUnit (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (d : ∀ T : GeometricSpace D, SpaceData l D T) :
    letI := (d T).units
    letI := (d U).units
    canonicalCommonStagePullbackTensor_unit l (PadicAlgCl l) g.hom := by
  let := (d T).units
  let := (d U).units
  have h := derivedPullbackTensorIso l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l)
      ⟨⊥, inferInstance⟩)
    g.hom 0 (PadicAlgCl l)
  tauto

/-- Exact reindexing and balanced scalar extension descend to the raw common-stage category.
Source: Bhatt--Scholze, Remark 6.8.15; HRS Lemma 7.9, integral comparison and descent
(blueprint: lem-sf-adic-reindexing-core).

Proof: Use sectionwise inverse image along each underlying scheme isomorphism. Its
coefficient map fixes the finite-extension-valued functions, and coefficient naturality
identifies the integral quotient projections and finite scalar transitions. Balanced scalar
extension gives the section-normalized IntegralReindex. Localize its cochain comparison
through the exact-derived factorizations and scalar-extension counits. Compose its inverse
with the specified completion-unit inverse and the integral realization isomorphisms; this
is precisely integralRealizationAgreement, including both mapping-fiber coordinates.
The scalar-compatibility equation for the specified completion unit makes these components
compatible with finite scalar extension. Naturality first descends through the raw finite
rationalizations and then through common-stage Hom groups: represent an arrow at a common
field, use naturality there, and cancel the two scalar comparisons. Equality at a larger
stage proves independence of representatives. The inverse components descend by the same
square. Construct tensor reindexing on total K-flat models by the homogeneous pure-tensor
map and descend it by the representative equation. Reindexing preserves K-flatness since
it is an exact monoidal equivalence. The coefficient unit pulls back to itself, supplying
the canonical common-stage unit assertion. For the ordinary identity and compositor use
sectionwise identity maps. For the source identity use the integral pullback identity and
descend it through rationalization and common-stage inclusion; its unit equation is the
identity of the specified pullback composition on the same representatives. These maps
retain the given objectwise data exactly. No linearity over the base field is used. -/
theorem exists_normalized_reindexing_core
    (d : ∀ T : GeometricSpace D, SpaceData l D T) :
    ∃ C : FamilyCore l D, C.data = d ∧
    (∀ (T : GeometricSpace D) (M : modules l T.base.left (C.data T).realization)
      (U : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (𝟙 _) (C.ring T T (Iso.refl _))).obj M).val.obj U),
    HEq (((C.moduleId T).hom.app M).val.app U x) x)
    ∧ (∀ (T U V : GeometricSpace D)
      (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
      (M : modules l V.base.left (C.data V).realization) (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (C.ring T V (g ≪≫ h))).obj M).val.obj W),
    HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    ∧ (∀ (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
      (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)),
    letI := (C.data T).units
    letI := (C.data U).units
    integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
      (C.ring T U g) E (C.integral T U g E) (C.comparison T U g))
    ∧ (∀ (T : GeometricSpace D)
      (M : generalAlgebraicallyClosedConstructibleCategory l (PadicAlgCl l) T.base.left),
    letI := (C.data T).units
    HEq
      ((pullbackTensorCommonComposition l (PadicAlgCl l)
          (𝟙 T.base.left) (𝟙 T.base.left) M).hom ≫
        (C.sourceId T).hom.app
          ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))
      (𝟙 ((commonStageDerivedPullback l (PadicAlgCl l) (𝟙 T.base.left)).obj M))) := by
  classical
  let B (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left) :=
    Classical.choice (exists_function_normalized_ring_reindex l g
      (d T).realization (d U).realization)
  have hi (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left) :=
    exists_integral_realization_reindexing l D d T U g (B T U g)
  choose I c hc using hi
  have hs (T : GeometricSpace D) := by
    letI := (d T).units
    exact exists_common_pullback_identity_unit l D T
  choose s hs using hs
  let C : FamilyCore l D :=
    { data := d
      ring := B
      integral := I
      moduleId := fun T ↦ normalizedModuleId l D T (d T).realization (B T T (Iso.refl _))
      moduleComp := fun T U V g h ↦
        normalizedModuleComp l D T U V g h (d T).realization (d U).realization
          (d V).realization (B T V (g ≪≫ h)) (B T U g) (B U V h)
      comparison := c
      sourceId := s
      pullTensor := fun T U g ↦ by
        letI := (d T).units
        letI := (d U).units
        exact Classical.choice (exists_tensor_reindexing_models l g
          (d T).realization (d U).realization (d T).tensor (d U).tensor (B T U g))
      unit_spec := fun T U g ↦ sourceUnit l D T U g d }
  refine ⟨C, rfl, ?_, ?_, ?_, ?_⟩
  · intro T M U x
    exact normalizedModuleId_sections l D T (d T).realization (B T T (Iso.refl _)) M U x
  · intro T U V g h M W x
    exact normalizedModuleComp_sections l D T U V g h (d T).realization
      (d U).realization (d V).realization (B T V (g ≪≫ h)) (B T U g) (B U V h) M W x
  · exact hc
  · exact hs

end WeilConjectures.AdicQbarRealization
