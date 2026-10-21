/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.ProEtaleConstantModulePullbackHomology
public import Sheaf.Paper.ProEtaleConstantModuleEncoding
public import WeilConjectures.ConstructibleSheaf.Pullback
import all Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import all Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated
import Sheaf.Paper.ProEtaleConstantModulePullbackComposition
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral

/-!
# Intrinsic finite-coefficient derived pullback

Source: Bhatt--Scholze, Lemmas 6.5.8(2), 6.5.9(5), finite discrete specialization,
and the intrinsic stratification argument isolated from Lemma 6.7.11;
Stacks Project, Tags 04JC, 015F, 010N, 054I, 03D8, 093R and 05V1
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

These are ordinary uncompleted derived categories of constant-ring module sheaves.
The pullback uses the existing tensor extension along the canonical constant-section map.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def modelPresheaf (C : Type*) [Category* C]
    (A : Type u) [CommRing A] : ModuleCat.{u + 1} (ULift.{u + 1, u} A) ⥤
      PresheafOfModules.{u + 1}
        ((Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A))) where
  obj := proEtaleConstantModulePresheaf C A
  map f := { app := fun _ ↦ f }

/-- Constant module presheaves are left adjoint to evaluation at a terminal object. -/
private noncomputable def modelPresheafAdj
    (C : Type*) [Category* C] (A : Type u) [CommRing A]
    {T : C} (hT : IsTerminal T) :
    modelPresheaf C A ⊣ PresheafOfModules.evaluation _ (Opposite.op T) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M P ↦
        { toFun := fun f ↦ f.app (Opposite.op T)
          invFun := fun f ↦
            { app := fun U ↦ ModuleCat.ofHom
                { toFun := fun m ↦ P.map (hT.from U.unop).op (f m)
                  map_add' := fun m n ↦ by
                    change P.map _ (f (m + n)) = _
                    rw [map_add, map_add]
                  map_smul' := fun a m ↦ by
                    rw [map_smul, PresheafOfModules.map_smul]
                    rfl }
              naturality := fun {U V} g ↦ by
                ext m
                change P.map (hT.from V.unop).op (f m) =
                  P.map g (P.map (hT.from U.unop).op (f m))
                rw [← PresheafOfModules.map_comp_apply]
                change P.map (hT.from V.unop).op (f m) =
                  P.map (g.unop ≫ hT.from U.unop).op (f m)
                rw [hT.hom_ext (g.unop ≫ hT.from U.unop) (hT.from V.unop)] }
          left_inv := fun f ↦ by
            ext U m
            change P.map (hT.from U.unop).op (f.app (Opposite.op T) m) = f.app U m
            exact (PresheafOfModules.naturality_apply f (hT.from U.unop).op m).symm
          right_inv := fun f ↦ by
            ext m
            change P.map (hT.from T).op (f m) = f m
            rw [hT.hom_ext (hT.from T) (𝟙 T)]
            exact ConcreteCategory.congr_hom (P.presheaf.map_id (Opposite.op T)) (f m) }
      homEquiv_naturality_left_symm := by intros; rfl
      homEquiv_naturality_right := by intros; rfl }

private noncomputable def modelSheafAdj
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    (A : Type u) [CommRing A] {R : Sheaf J RingCat.{u + 1}}
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {T : C} (hT : IsTerminal T) :
    modelPresheaf C A ⋙ PresheafOfModules.sheafification.{u + 1} α ⊣
      SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.restrictScalars α ⋙
        PresheafOfModules.evaluation _ (Opposite.op T) :=
  (modelPresheafAdj C A hT).comp (PresheafOfModules.sheafificationAdjunction α)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def pullbackModelIso
    {C D : Type (u + 1)} [Category.{u + 1} C] [Category.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : C ⥤ D) [f.IsContinuous J K]
    (A : Type u) [CommRing A]
    {R : Sheaf J RingCat.{u + 1}} {S : Sheaf K RingCat.{u + 1}}
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)) ⟶ R.obj)
    (β : (Functor.const Dᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective K β] [Presheaf.IsLocallySurjective K β]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (φ : R ⟶ (f.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S)
    (hφ : α ≫ φ.hom = Functor.whiskerLeft f.op β)
    {T : C} (hT : IsTerminal T) (hFT : IsTerminal (f.obj T))
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    (SheafOfModules.pullback.{u + 1} φ).obj
        ((PresheafOfModules.sheafification.{u + 1} α).obj (proEtaleConstantModulePresheaf C A M)) ≅
      (PresheafOfModules.sheafification.{u + 1} β).obj (proEtaleConstantModulePresheaf D A M) := by
  let er := SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.restrictScalars α ⋙
    PresheafOfModules.evaluation _ (Opposite.op T)
  let es := SheafOfModules.forget.{u + 1} S ⋙ PresheafOfModules.restrictScalars β ⋙
    PresheafOfModules.evaluation _ (Opposite.op (f.obj T))
  let e : SheafOfModules.pushforward.{u + 1} φ ⋙ er ≅ es :=
    NatIso.ofComponents (fun N ↦
      (show ((SheafOfModules.pushforward.{u + 1} φ ⋙ er).obj N : Type (u + 1)) ≃ₗ[
          ULift.{u + 1, u} A] (es.obj N) from
        { toFun := fun m ↦ m
          invFun := fun m ↦ m
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun a m ↦ by
            change ((φ.hom.app (Opposite.op T)).hom ((α.app (Opposite.op T)).hom a)) •
                (show N.val.obj (Opposite.op (f.obj T)) from m) =
              (β.app (Opposite.op (f.obj T))).hom a •
                (show N.val.obj (Opposite.op (f.obj T)) from m)
            exact congrArg (fun r ↦ r • (show N.val.obj (Opposite.op (f.obj T)) from m))
              (ConcreteCategory.congr_hom (congr_app hφ (Opposite.op T)) a) }).toModuleIso)
      (fun _ ↦ by ext m; rfl)
  let adjR := (modelPresheafAdj C A hT).comp
    (PresheafOfModules.sheafificationAdjunction α)
  let adjS := (modelPresheafAdj D A hFT).comp
    (PresheafOfModules.sheafificationAdjunction β)
  let adj := (adjR.comp (SheafOfModules.pullbackPushforwardAdjunction φ)).ofNatIsoRight e
  exact (adj.leftAdjointUniq adjS).app M

private abbrev siteUp {C : Type (u + 1)} [Category.{u} C] : C ⥤ AsSmall.{u + 1} C :=
  AsSmall.up

private abbrev siteDown {C : Type (u + 1)} [Category.{u} C] : AsSmall.{u + 1} C ⥤ C :=
  AsSmall.down

private noncomputable abbrev smallRing (X : Scheme.{u}) (A : Type u) [CommRing A] :=
  ((siteDown : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)).obj
      (proEtaleConstantRing X A)

private noncomputable def toSmall (X : Scheme.{u}) (A : Type u) [CommRing A] :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      SheafOfModules.{u + 1}
        ((sheafCompose (proEtaleModelTopology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (smallRing X A)) :=
  proEtaleModuleToModel ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))

private noncomputable def smallCoefficientMap {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [CommRing A] :
    smallRing Y A ⟶ ((proEtaleModelBaseChange h).sheafPushforwardContinuous
      CommRingCat.{u + 1} (proEtaleModelTopology Y) (proEtaleModelTopology X)).obj
        (smallRing X A) :=
  ⟨Functor.whiskerLeft siteDown.op (proEtaleCoefficientDirectImageMap h A).hom⟩

private local instance smallDownEquivalence (X : Scheme.{u}) :
    (siteDown : proEtaleSiteModel X ⥤ X.ProEt).IsEquivalence :=
  inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsEquivalence

private local instance smallUpEquivalence (X : Scheme.{u}) :
    (siteUp : X.ProEt ⥤ proEtaleSiteModel X).IsEquivalence :=
  inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsEquivalence

private local instance smallBaseChangeLimits {X Y : Scheme.{u}} (h : X ⟶ Y) :
    PreservesFiniteLimits (proEtaleModelBaseChange h) := by
  unfold proEtaleModelBaseChange
  infer_instance

private local instance smallBaseChangeFlat {X Y : Scheme.{u}} (h : X ⟶ Y) :
    RepresentablyFlat (proEtaleModelBaseChange h) := flat_of_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency false in
private theorem smallPullbackIso {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) :
    Nonempty ((toSmall X A).obj (proEtaleConstantModulePullback h A F) ≅
      (SheafOfModules.pullback.{u + 1}
        (SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange h)
          (smallCoefficientMap h A))).obj ((toSmall Y A).obj F)) := by
  let RX := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing X A)
  let RY := (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (proEtaleConstantRing Y A)
  let EX := (proEtaleModuleModelEquivalence X RX).symm
  let EY := (proEtaleModuleModelEquivalence Y RY).symm
  let φ := SheafOfModules.ringedSiteModuleMap (proEtaleModelBaseChange h)
    (smallCoefficientMap h A)
  let ψ : RY ⟶ ((proEtaleBaseChange h).sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X)).obj RX :=
    ⟨Functor.whiskerRight (proEtaleCoefficientDirectImageMap h A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let eR : EX.functor ⋙ SheafOfModules.pushforward.{u + 1} φ ⋙ EY.inverse ≅
      SheafOfModules.pushforward.{u + 1} ψ :=
    NatIso.ofComponents (fun N ↦
      { hom :=
          { val :=
              { app := fun U ↦
                  ConcreteCategory.ofHom (C := ModuleCat.{u + 1} (RY.obj.obj U))
                  { toFun := fun m ↦ m
                    map_add' := fun _ _ ↦ rfl
                    map_smul' := fun _ _ ↦ rfl }
                naturality := fun _ ↦ by ext m; rfl } }
        inv :=
          { val :=
              { app := fun U ↦
                  ConcreteCategory.ofHom (C := ModuleCat.{u + 1} (RY.obj.obj U))
                  { toFun := fun m ↦ m
                    map_add' := fun _ _ ↦ rfl
                    map_smul' := fun _ _ ↦ rfl }
                naturality := fun _ ↦ by ext m; rfl } }
        hom_inv_id := by ext U m; rfl
        inv_hom_id := by ext U m; rfl }) (fun _ ↦ by ext U m; rfl)
  let adj₀ := EY.toAdjunction.comp
    ((SheafOfModules.pullbackPushforwardAdjunction φ).comp EX.symm.toAdjunction)
  let adj := adj₀.ofNatIsoRight eR
  have := constantComparison_isIso h A
  let adjActual := proEtaleRingModuleAdjunction h (proEtaleConstantRing Y A)
    (proEtaleConstantRing X A) (asIso (proEtaleCoefficientInverseImageMap h A))
  change proEtaleConstantModulePullbackFunctor h A ⊣ _ at adjActual
  dsimp only [proEtaleRingModuleDirectImage] at adjActual
  rw [proEtaleConstantModulePullback_ring_direct] at adjActual
  let e := adjActual.leftAdjointUniq adj
  exact ⟨EX.functor.mapIso (e.app F) ≪≫
    EX.counitIso.app ((SheafOfModules.pullback.{u + 1} φ).obj (EY.functor.obj F))⟩

private noncomputable def smallSliceEquivalence (Y : Scheme.{u}) (U : Y.ProEt) :
    Over ((siteUp : Y.ProEt ⥤ proEtaleSiteModel Y).obj U) ≌ Over U where
  functor := Over.post siteDown
  inverse := Over.post siteUp
  unitIso := NatIso.ofComponents (fun V ↦ Over.isoMk (Iso.refl _))
  counitIso := NatIso.ofComponents (fun V ↦ Over.isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def smallSliceModules (Y : Scheme.{u}) (U : Y.ProEt) (A : Type u)
    [CommRing A] :
    SheafOfModules.{u + 1}
        (((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing Y A)).over U) ≌
      SheafOfModules.{u + 1}
        ((((siteDown : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj
            ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (proEtaleConstantRing Y A))).over (siteUp.obj U)) := by
  have hd : (Over.post (X := siteUp.obj U)
      (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)).IsContinuous
        ((proEtaleModelTopology Y).over (siteUp.obj U)) ((ProEt.topology Y).over U) :=
    Functor.isContinuous_iff_coverPreserving.mpr
      ((CoverPreserving.of_isContinuous
        (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)
          (proEtaleModelTopology Y) (ProEt.topology Y)).overPost (siteUp.obj U))
  have hu : (Over.post (X := U) (siteUp : Y.ProEt ⥤ proEtaleSiteModel Y)).IsContinuous
      ((ProEt.topology Y).over U) ((proEtaleModelTopology Y).over (siteUp.obj U)) :=
    Functor.isContinuous_iff_coverPreserving.mpr
      ((CoverPreserving.of_isContinuous
        (siteUp : Y.ProEt ⥤ proEtaleSiteModel Y)
          (ProEt.topology Y) (proEtaleModelTopology Y)).overPost U)
  have : (smallSliceEquivalence Y U).functor.IsContinuous
      ((proEtaleModelTopology Y).over (siteUp.obj U))
        ((ProEt.topology Y).over U) := hd
  have : (smallSliceEquivalence Y U).inverse.IsContinuous
      ((ProEt.topology Y).over U)
        ((proEtaleModelTopology Y).over (siteUp.obj U)) := hu
  let R := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (smallSliceEquivalence Y U) (𝟙 _) (𝟙 _)
    (by
      apply NatTrans.ext
      funext V
      change R.obj.map (𝟙 _) = _
      rw [R.obj.map_id]
      rfl)
    (by
      apply NatTrans.ext
      funext V
      change R.obj.map (𝟙 _) = _
      rw [R.obj.map_id]
      rfl)

private local instance overUnitInjective (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (U : Y.ProEt) : Presheaf.IsLocallyInjective ((ProEt.topology Y).over U)
      (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit Y A)) :=
  (proEtaleConstantRingUnit_over_locallyBijective Y A U).1

private local instance overUnitSurjective (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (U : Y.ProEt) : Presheaf.IsLocallySurjective ((ProEt.topology Y).over U)
      (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit Y A)) :=
  (proEtaleConstantRingUnit_over_locallyBijective Y A U).2

private local instance smallDownCocontinuous (Y : Scheme.{u}) :
    (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt).IsCocontinuous
      (proEtaleModelTopology Y) (ProEt.topology Y) := by
  change siteDown.IsCocontinuous
    (siteDown.inducedTopology (ProEt.topology Y)) (ProEt.topology Y)
  infer_instance

private local instance smallOverDownCocontinuous (Y : Scheme.{u}) (U : Y.ProEt) :
    (Over.post (X := siteUp.obj U)
      (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)).IsCocontinuous
        ((proEtaleModelTopology Y).over (siteUp.obj U)) ((ProEt.topology Y).over U) := by
  exact inferInstanceAs ((Over.post (X := siteUp.obj U)
    (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)).IsCocontinuous
      ((proEtaleModelTopology Y).over (siteUp.obj U))
        ((ProEt.topology Y).over (siteDown.obj (siteUp.obj U))))

private local instance smallOverUnitInjective (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (U : Y.ProEt) :
    Presheaf.IsLocallyInjective ((proEtaleModelTopology Y).over (siteUp.obj U))
      (Functor.whiskerLeft (Over.post (X := siteUp.obj U)
        (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)).op
          (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit Y A))) :=
  by
    let := smallOverDownCocontinuous Y U
    exact Presheaf.isLocallyInjective_whisker
      ((proEtaleModelTopology Y).over (siteUp.obj U))
      ((ProEt.topology Y).over U)
      (Over.post (X := siteUp.obj U)
        (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)) _

private local instance smallOverUnitSurjective (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (U : Y.ProEt) :
    Presheaf.IsLocallySurjective ((proEtaleModelTopology Y).over (siteUp.obj U))
      (Functor.whiskerLeft (Over.post (X := siteUp.obj U)
        (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)).op
          (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit Y A))) :=
  by
    let := smallOverDownCocontinuous Y U
    exact Presheaf.isLocallySurjective_whisker
      ((proEtaleModelTopology Y).over (siteUp.obj U))
      ((ProEt.topology Y).over U)
      (Over.post (X := siteUp.obj U)
        (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)) _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def smallSliceConstantIso (Y : Scheme.{u}) (U : Y.ProEt)
    (A : Type u) [CommRing A] (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    (smallSliceModules Y U A).functor.obj (proEtaleConstantModuleSheafOver Y A U M) ≅
      (PresheafOfModules.sheafification.{u + 1} (R :=
        (((siteDown : proEtaleSiteModel Y ⥤ Y.ProEt).sheafPushforwardContinuous
          RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj
            ((sheafCompose (ProEt.topology Y)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
                (proEtaleConstantRing Y A))).over (siteUp.obj U))
        (Functor.whiskerLeft (Over.post (X := siteUp.obj U)
          (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)).op
            (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit Y A)))).obj
              (proEtaleConstantModulePresheaf (Over (siteUp.obj U)) A M) := by
  let E := smallSliceModules Y U A
  let R := ((sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)).over U
  let S := (((siteDown : proEtaleSiteModel Y ⥤
      Y.ProEt).sheafPushforwardContinuous
    RingCat.{u + 1} (proEtaleModelTopology Y) (ProEt.topology Y)).obj
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (proEtaleConstantRing Y A))).over (siteUp.obj U)
  let α : (Functor.const (Over U)ᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)) ⟶ R.obj :=
    Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit Y A)
  let β : (Functor.const (Over (siteUp.obj U))ᵒᵖ).obj
      (RingCat.of (ULift.{u + 1, u} A)) ⟶ S.obj :=
    Functor.whiskerLeft (Over.post (X := siteUp.obj U)
      (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)).op α
  have hiα := (proEtaleConstantRingUnit_over_locallyBijective Y A U).1
  have hsα := (proEtaleConstantRingUnit_over_locallyBijective Y A U).2
  have hiβ : Presheaf.IsLocallyInjective
      ((proEtaleModelTopology Y).over (siteUp.obj U)) β := inferInstance
  have hsβ : Presheaf.IsLocallySurjective
      ((proEtaleModelTopology Y).over (siteUp.obj U)) β := inferInstance
  let er := SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.restrictScalars α ⋙
    PresheafOfModules.evaluation _ (Opposite.op (Over.mk (𝟙 U)))
  let es := SheafOfModules.forget.{u + 1} S ⋙ PresheafOfModules.restrictScalars β ⋙
    PresheafOfModules.evaluation _ (Opposite.op (Over.mk (𝟙 (siteUp.obj U))))
  let eR : E.inverse ⋙ er ≅ es :=
    NatIso.ofComponents (fun N ↦
      (show ((E.inverse ⋙ er).obj N : Type (u + 1)) ≃ₗ[ULift.{u + 1, u} A]
          (es.obj N) from
        { toFun := fun m ↦ m
          invFun := fun m ↦ m
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }).toModuleIso) (fun _ ↦ by ext m; rfl)
  let adj := ((modelSheafAdj A α (Over.mkIdTerminal (X := U))).comp
    E.toAdjunction).ofNatIsoRight eR
  exact (adj.leftAdjointUniq
    (modelSheafAdj A β (Over.mkIdTerminal (X := siteUp.obj U)))).app M

set_option backward.isDefEq.respectTransparency false in
private theorem pullbackOverModel {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEt)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A))
    (e : F.over U ≅ proEtaleConstantModuleSheafOver Y A U M) :
    Nonempty ((proEtaleConstantModulePullback h A F).over ((proEtaleBaseChange h).obj U) ≅
      proEtaleConstantModuleSheafOver X A ((proEtaleBaseChange h).obj U) M) := by
  let f := proEtaleModelBaseChange h
  let V := (siteUp : Y.ProEt ⥤ proEtaleSiteModel Y).obj U
  let W := (proEtaleBaseChange h).obj U
  let a := smallCoefficientMap h A
  let fm := (proEtaleModuleToModel
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (proEtaleConstantRing Y A))).obj F
  have : RepresentablyFlat f := smallBaseChangeFlat h
  have : PreservesFiniteLimits
      (f.sheafPullback (Type (u + 1)) (proEtaleModelTopology Y) (proEtaleModelTopology X)) :=
    Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
      f (Type (u + 1)) (proEtaleModelTopology Y) (proEtaleModelTopology X)
  obtain ⟨hc, hl, es, er, hr, eloc, edir, he⟩ :=
    SheafOfModules.localize_ringed_site_morphism_general f a V
  let α := Functor.whiskerLeft (Over.post (X := V)
    (siteDown : proEtaleSiteModel Y ⥤ Y.ProEt)).op
      (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit Y A))
  let β := Functor.whiskerLeft (Over.post (X := f.obj V)
    (siteDown : proEtaleSiteModel X ⥤ X.ProEt)).op
      (Functor.whiskerLeft (Over.forget W).op (proEtaleModuleScalarUnit X A))
  have hiα : Presheaf.IsLocallyInjective ((proEtaleModelTopology Y).over V) α :=
    inferInstance
  have hsα : Presheaf.IsLocallySurjective ((proEtaleModelTopology Y).over V) α :=
    inferInstance
  have hiβ : Presheaf.IsLocallyInjective ((proEtaleModelTopology X).over (f.obj V)) β :=
    smallOverUnitInjective X A W
  have hsβ : Presheaf.IsLocallySurjective ((proEtaleModelTopology X).over (f.obj V)) β :=
    smallOverUnitSurjective X A W
  let φ := SheafOfModules.ringedSiteModuleMap (Over.post (X := V) f)
    (SheafOfModules.localizedRingedSiteMap f a V)
  have hφ : α ≫ φ.hom = Functor.whiskerLeft (Over.post (X := V) f).op β := by
    apply NatTrans.ext
    funext T
    exact congrArg (fun t ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map t)
      (proEtaleConstantModulePullback_rho_unit h A (Opposite.op (siteDown.obj T.unop.left)))
  let EY := smallSliceModules Y U A
  let EX := smallSliceModules X W A
  let em : fm.over V ≅ (PresheafOfModules.sheafification.{u + 1} α).obj
      (proEtaleConstantModulePresheaf (Over V) A M) :=
    EY.functor.mapIso e ≪≫ smallSliceConstantIso Y U A M
  have ht : IsTerminal ((Over.post (X := V) f).obj (Over.mk (𝟙 V))) :=
    (Over.mkIdTerminal (X := f.obj V)).ofIso
      (Over.isoMk (Iso.refl _) (by change 𝟙 _ ≫ f.map (𝟙 V) = 𝟙 _; simp))
  obtain ⟨ep⟩ := smallPullbackIso h A F
  refine ⟨EX.functor.preimageIso ?_⟩
  exact (SheafOfModules.overFunctor.{u + 1} _ (f.obj V)).mapIso ep ≪≫
    (eloc.app fm).symm ≪≫ (SheafOfModules.pullback.{u + 1} φ).mapIso em ≪≫
    pullbackModelIso (Over.post (X := V) f) A
      (R := (sheafCompose ((proEtaleModelTopology Y).over V)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj ((smallRing Y A).over V))
      (S := (sheafCompose ((proEtaleModelTopology X).over (f.obj V))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((smallRing X A).over (f.obj V))) α β φ hφ
      (Over.mkIdTerminal (X := V)) ht M ≪≫
    (smallSliceConstantIso X W A M).symm

/-- The specified constant-coefficient module pullback is additive and exact.
Source: Bhatt--Scholze, Lemma 6.5.9(5), finite discrete case; Stacks Tag 04JC
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node step 1): the canonical constant-coefficient pullback functor already
has additive, finite-limit-preserving and finite-colimit-preserving instances in
lem-pur-proetale-constant-module-pullback-homology. Apply those instances. These
hold for every commutative coefficient ring. -/
theorem intrinsicFiniteModulePullback_exact {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [Field A] [Finite A] :
    (proEtaleConstantModulePullbackFunctor h A).Additive ∧
      PreservesFiniteLimits (proEtaleConstantModulePullbackFunctor h A) ∧
      PreservesFiniteColimits (proEtaleConstantModulePullbackFunctor h A) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Termwise pullback descends to the ordinary unbounded derived category and
commutes naturally with every cohomology functor.
Source: Stacks Tags 015F and 010N; Bhatt--Scholze, Lemma 6.5.9(5), finite discrete case
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node step 2): apply lem-weil-pbc-exact-functor-derived-factorization to the
exact pullback. It preserves quasi-isomorphisms, so localization gives the displayed
factorization. The unbounded cohomology comparison in
lem-weil-pbc-exact-functor-bounded-below gives the natural isomorphism for every
integer q; the assertion does not require a bounded-below input. -/
theorem intrinsicFiniteModulePullback_derived {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [Field A] [Finite A] :
    Nonempty (DerivedCategory.Q ⋙
      (proEtaleConstantModulePullbackFunctor h A).mapDerivedCategory ≅
        (proEtaleConstantModulePullbackFunctor h A).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
    ∀ q : ℤ, Nonempty
      ((proEtaleConstantModulePullbackFunctor h A).mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor
            (proEtaleRingModules X (proEtaleConstantRing X A)) q ≅
        DerivedCategory.homologyFunctor
            (proEtaleRingModules Y (proEtaleConstantRing Y A)) q ⋙
          proEtaleConstantModulePullbackFunctor h A) := by
  exact ⟨⟨(proEtaleConstantModulePullbackFunctor h A).mapDerivedCategoryFactors⟩,
    fun q ↦
      ⟨((proEtaleConstantModulePullbackFunctor h A).mapDerivedCategoryHomologyFunctorIso q).symm⟩⟩

/-- Every given intrinsic witnessing stratification pulls back to a witnessing
stratification, with the same finite models on the actual base-changed covering.
The strata and their immersion maps are exactly `s.pullback h`, defined by fibre
products. Its number of strata is `s.n`, so it stays positive even when X is empty.
Source: Stacks Tags 054I, 03D8, 093R and 05V1; Bhatt--Scholze, Lemma 6.5.8(2)
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node steps 3--7): the existing pullback stratification uses actual fibre
products and retains all strata, so its positive number is unchanged, including
over the empty scheme. Composition of canonical module pullbacks and the
Cartesian equation identify the two restricted modules. The finite-local-constancy
pullback theorem supplies local constancy and finite stalks; the equivalence
between intrinsic and fixed-module stalk finiteness supplies finite generation.
Base change preserves the given covering by the precoverage pullback axiom.
For each member, localize the ringed module pullback on the universe-compatible
small site. The constant module presheaf is left adjoint to evaluation at a
terminal object; after sheafification it is left adjoint to sections with scalars
restricted along the constant-ring unit. The coefficient direct image fixes
constant sections. Uniqueness of left adjoints therefore shows that localized
pullback preserves the exact same model. Transport this comparison along the
small-site equivalence, using the same adjunction argument for constant models,
and compose it with the restriction-composition isomorphism. The private helpers
above implement these comparisons, without identifying a slice with the site of
the covering scheme. -/
theorem intrinsicFiniteModulePullback_stratification {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [Field A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (s : Stratification Y) (_hn : 0 < s.n)
    (_hs : ∀ i : Fin s.n,
      IsLocallyConstantProEtaleModuleSheaf (s.domain i) A
          (proEtaleConstantModulePullback (s.immersion i) A F) ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ s.domain i),
          Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing (s.domain i) A)
            (proEtaleConstantModulePullback (s.immersion i) A F))) :
    ∀ i : Fin s.n,
      IsLocallyConstantProEtaleModuleSheaf ((s.pullback h).domain i) A
          (proEtaleConstantModulePullback ((s.pullback h).immersion i) A
            (proEtaleConstantModulePullback h A F)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
          (x : Spec (.of Ω) ⟶ (s.pullback h).domain i),
        Finite (proEtaleGeometricModuleStalk x
          (proEtaleConstantRing ((s.pullback h).domain i) A)
          (proEtaleConstantModulePullback ((s.pullback h).immersion i) A
            (proEtaleConstantModulePullback h A F))) ∧
        Module.Finite (ULift.{u + 1, u} A)
          (proEtaleGeometricFixedModuleStalk x (ULift.{u + 1, u} A)
            ((proEtaleModuleRestriction ((s.pullback h).domain i) A).obj
              (proEtaleConstantModulePullback ((s.pullback h).immersion i) A
                (proEtaleConstantModulePullback h A F))))) ∧
      Nonempty
        (proEtaleConstantModulePullback ((s.pullback h).immersion i) A
            (proEtaleConstantModulePullback h A F) ≅
          proEtaleConstantModulePullback (pullback.fst (s.immersion i) h) A
            (proEtaleConstantModulePullback (s.immersion i) A F)) ∧
      ∀ (I : Type (u + 1)) (U : I → (s.domain i).ProEt)
        (a : ∀ j : I, U j ⟶ ProEt.mk (𝟙 (s.domain i))),
        Presieve.ofArrows U a ∈ (ProEt.precoverage (s.domain i)).coverings _ →
        ∀ M : I → ModuleCat.{u + 1} (ULift.{u + 1, u} A),
          (∀ j : I, Finite (M j)) →
          (∀ j : I, Nonempty
            ((proEtaleConstantModulePullback (s.immersion i) A F).over (U j) ≅
              proEtaleConstantModuleSheafOver (s.domain i) A (U j) (M j))) →
          ∃ b : ∀ j : I,
              (proEtaleBaseChange (pullback.fst (s.immersion i) h)).obj (U j) ⟶
                ProEt.mk (𝟙 ((s.pullback h).domain i)),
            Presieve.ofArrows
                (fun j : I ↦
                  (proEtaleBaseChange (pullback.fst (s.immersion i) h)).obj (U j)) b ∈
              (ProEt.precoverage ((s.pullback h).domain i)).coverings _ ∧
            ∀ j : I, Nonempty
              ((proEtaleConstantModulePullback ((s.pullback h).immersion i) A
                  (proEtaleConstantModulePullback h A F)).over
                    ((proEtaleBaseChange (pullback.fst (s.immersion i) h)).obj (U j)) ≅
                proEtaleConstantModuleSheafOver ((s.pullback h).domain i) A
                  ((proEtaleBaseChange (pullback.fst (s.immersion i) h)).obj (U j)) (M j)) := by
  intro i
  let p : (s.pullback h).domain i ⟶ s.domain i := pullback.fst (s.immersion i) h
  let G := proEtaleConstantModulePullback (s.immersion i) A F
  let H := proEtaleConstantModulePullback ((s.pullback h).immersion i) A
    (proEtaleConstantModulePullback h A F)
  obtain ⟨e₁⟩ := proEtaleConstantModulePullback_comp h ((s.pullback h).immersion i) A
  obtain ⟨e₂⟩ := proEtaleConstantModulePullback_comp (s.immersion i) p A
  let e : H ≅ proEtaleConstantModulePullback p A G :=
    (e₁.app F).symm ≪≫
      eqToIso (congrArg (fun f ↦ proEtaleConstantModulePullback f A F)
        (pullback.condition (f := s.immersion i) (g := h)).symm) ≪≫ e₂.app F
  have hp := proEtale_finiteLocalConstancy_pullback p A G (_hs i)
  refine ⟨locallyConstant_of_iso _ A e.symm hp.1, ?_, ⟨e⟩, ?_⟩
  · intro Ω _ _ x
    have := hp.2 Ω x
    have hf : Finite (proEtaleGeometricModuleStalk x
        (proEtaleConstantRing ((s.pullback h).domain i) A) H) :=
      finite_stalk_of_iso _ A e.symm x
    have := (finite_stalk_iff _ A H Ω x).mp hf
    exact ⟨hf, inferInstance⟩
  · intro I U a ha M _hM hM
    let b (j : I) : (proEtaleBaseChange p).obj (U j) ⟶
        ProEt.mk (𝟙 ((s.pullback h).domain i)) :=
      MorphismProperty.Over.homMk (pullback.snd (U j).hom p) (Category.comp_id _)
    refine ⟨b, ?_, fun j ↦ ?_⟩
    · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
      have ha' : Presieve.ofArrows (fun j ↦ (U j).left) (fun j ↦ (U j).hom) ∈
          Scheme.proetalePrecoverage (s.domain i) := by
        rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows] at ha
        have heq (j : I) : (a j).left = (U j).hom := by
          exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w (a j))
        change Presieve.ofArrows (fun j ↦ (U j).left) (fun j ↦ (a j).left) ∈
          Scheme.proetalePrecoverage (s.domain i) at ha
        simpa only [heq] using ha
      exact Precoverage.mem_coverings_of_isPullback (fun j ↦ (U j).hom) ha' p _ _
        (fun j ↦ (IsPullback.of_hasPullback (U j).hom p).flip)
    · obtain ⟨em⟩ := hM j
      obtain ⟨ep⟩ := pullbackOverModel p A G (U j) (M j) em
      exact ⟨(SheafOfModules.overFunctor.{u + 1} _
        ((proEtaleBaseChange p).obj (U j))).mapIso e ≪≫ ep⟩

/-- Intrinsic constructibility is preserved for every scheme morphism.
Source: Bhatt--Scholze, Lemmas 6.5.8(2) and 6.5.9(5), finite discrete specialization
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node steps 3--7): unpack the positive finite witnessing stratification,
base-change its strata and local trivializing covers, and use the restriction
composition isomorphism and the same constant module models as above. Stalk
comparison preserves their finiteness. The number of strata remains positive,
including for the empty scheme, whose module sheaf is zero. These data satisfy
exactly def-weil-proetale-constructible-sheaf. -/
theorem intrinsicFiniteModulePullback_constructible {X Y : Scheme.{u}} (h : X ⟶ Y)
    (A : Type u) [Field A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (_hF : IsConstructibleProEtaleModuleSheaf Y A F) :
    IsConstructibleProEtaleModuleSheaf X A (proEtaleConstantModulePullback h A F) := by
  obtain ⟨s, hn, hs⟩ := _hF
  refine ⟨s.pullback h, hn, fun i ↦ ?_⟩
  obtain ⟨hl, hf, _⟩ := intrinsicFiniteModulePullback_stratification h A F s hn hs i
  exact ⟨hl, fun Ω _ _ x ↦ (hf Ω x).1⟩

/-- Ordinary derived pullback preserves bounded intrinsic constructibility with
any specified cohomological vanishing interval unchanged.
Source: Bhatt--Scholze, Lemma 6.5.9(5), R = A and m = 0; Stacks Tag 015F
(blueprint: lem-sfb-intrinsic-finite-derived-pullback).

Proof (node step 8): use the natural cohomology isomorphism of step 2. The pullback
of each constructible cohomology sheaf is constructible by steps 3--7. Outside
[a,b] its source is zero, so exact additive pullback is zero too. Thus the same
interval works. The earlier arguments use arbitrary scheme maps and ordinary
constant-ring modules; no characteristic restriction, cohomological-dimension
bound or Noetherian hypothesis occurs. -/
theorem intrinsicFiniteDerivedPullback_bounded_constructible
    {X Y : Scheme.{u}} (h : X ⟶ Y) (A : Type u) [Field A] [Finite A]
    (K : proEtaleDerivedCategory Y A) (a b : ℤ) (_hab : a ≤ b)
    (_hvanish : ∀ q : ℤ, (q < a ∨ b < q) → IsZero
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) q).obj K))
    (_hconstructible : ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf Y A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) q).obj K)) :
    (∀ q : ℤ, (q < a ∨ b < q) → IsZero
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj
          ((proEtaleConstantModulePullbackFunctor h A).mapDerivedCategory.obj K))) ∧
    ∀ q : ℤ, IsConstructibleProEtaleModuleSheaf X A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X A)) q).obj
          ((proEtaleConstantModulePullbackFunctor h A).mapDerivedCategory.obj K)) := by
  constructor
  · intro q hq
    let e := (proEtaleConstantModulePullbackFunctor h A).mapDerivedCategoryHomologyFunctorIso q
    exact ((proEtaleConstantModulePullbackFunctor h A).map_isZero (_hvanish q hq)).of_iso
      (e.symm.app K)
  · intro q
    exact constructibleProEtale_of_iso X A
      (((proEtaleConstantModulePullbackFunctor h A).mapDerivedCategoryHomologyFunctorIso q).app K)
      (intrinsicFiniteModulePullback_constructible h A _ (_hconstructible q))

end AlgebraicGeometry.Scheme
