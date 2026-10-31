/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SiteSumGeneratorNormalization
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteConstantCoefficientTransport
import all WeilConjectures.AlgebraicGeometry.FiniteConstantCoefficientTransport
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarCoherence
import WeilConjectures.AlgebraicGeometry.UnboundedProperOpenPastingSupplement
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportNormalizationDataSupplement
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent

/-! # The ordinary graph-map square across the site comparison

Source: `WeilConjectures.AlgebraicGeometry.VaryingRingGraphSummand`, finite_normalization proof, step 2;
Stacks Project, Tags 0F4L, 09A5 and 09AF; current blueprint `det-sp-tower-gluing`,
Local pairs (blueprint: lem-sp-graph-map-site-square).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.VaryingRingGraph

open StrictTower

set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true

private theorem comparison_sum_hom_ext (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] {U T : Scheme.{u}} (e : U ⟶ T) [Etale e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (Y : Modules A T)
    (f g : (sitePull A T).obj
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) ⟶ Y)
    (h : ∀ (W : U.Etale) (m : M.obj.obj (op W)),
      f.val.app (op ((toProEt T).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
        (siteSumUnitSection A T
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
          (etaleSumLiftGenerator A e M W m)) =
      g.val.app (op ((toProEt T).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
        (siteSumUnitSection A T
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
          (etaleSumLiftGenerator A e M W m))) : f = g := by
  let E := fixedRestriction A T
  have : E.IsEquivalence := fixedRestriction_equivalence A T
  let D := sheafCompose (ProEt.topology T)
    (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) T).obj
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)
  have hiso : D.mapIso ((cFixed A T A (RingHom.id A)).app F) =
      (cUnderlying A T A (RingHom.id A)).app F := Iso.ext (by rfl)
  have hi := congrArg Iso.inv hiso
  apply E.map_injective
  apply (cancel_epi ((cFixed A T A (RingHom.id A)).inv.app F)).1
  apply ((comparisonAdjunction (ModuleCat.{u + 1} A) T).homEquiv _ _).injective
  apply ((Etale.etaleLowerShriekRestrictionAdjunction
    (ModuleCat.{u + 1} A) e).homEquiv _ _).injective
  apply Sheaf.hom_ext
  ext W m
  cases W using Opposite.rec
  rename_i W
  simp only [Adjunction.homEquiv_unit, Etale.etaleLowerShriekRestrictionAdjunction,
    Adjunction.ofNatIsoRight_unit, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    Etale.localizationRestriction_map_hom_app, ModuleCat.comp_apply]
  change f.val.app _
    (((cFixed A T A (RingHom.id A)).inv.app F).hom.app _
      (((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app _).hom.app _
        (etaleSumLiftGenerator A e M W m))) =
    g.val.app _
    (((cFixed A T A (RingHom.id A)).inv.app F).hom.app _
      (((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app _).hom.app _
        (etaleSumLiftGenerator A e M W m)))
  have hiv := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u + 1})
    (congrArg (fun z ↦ z.hom.app
      (op ((toProEt T).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))) hi)
    (((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app _).hom.app _
      (etaleSumLiftGenerator A e M W m))
  change (((cFixed A T A (RingHom.id A)).inv.app F).hom.app _) _ =
    (((cUnderlying A T A (RingHom.id A)).inv.app F).hom.app _) _ at hiv
  exact (congrArg (fun z ↦ f.val.app _ z) hiv).trans
    ((h W m).trans (congrArg (fun z ↦ g.val.app _ z) hiv).symm)

private theorem site_sum_generator (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] {U T : Scheme.{u}} (e : U ⟶ T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (m : M.obj.obj (op W)) :
    ((@asIso _ _ _ _ (siteSumInv A e) (siteSumInv_isIso A e)).inv.app M).val.app
      (op ((toProEt T).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
      (siteSumUnitSection A T
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
        (etaleSumLiftGenerator A e M W m)) =
      levelGenerator A e ((sitePull A U).obj M) ((toProEt U).obj W)
        (siteSumUnitSection A U M W m) := by
  obtain ⟨a, ha, hu, hc, hg⟩ := siteSum_generator_normalization A e
  have hi : a.symm = @asIso _ _ _ _ (siteSumInv A e) (siteSumInv_isIso A e) :=
    Iso.ext ha
  have hh := congrArg Iso.inv hi
  change a.hom = _ at hh
  rw [← hh]
  exact hg M W m

private theorem site_open_generator (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (m : M.obj.obj (op W)) :
    ((hOpen A j A (RingHom.id A)).app M).val.app
      (op ((toProEt X).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj W)))
      (siteSumUnitSection A X
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj M)
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj W)
        (etaleSumLiftGenerator A j M W m)) =
      levelGenerator A j ((sitePull A U).obj M) ((toProEt U).obj W)
        (siteSumUnitSection A U M W m) := by
  obtain ⟨a, ha, hu, hc, hg⟩ := siteSum_generator_normalization A j
  have hi : a.symm = @asIso _ _ _ _ (hOpenInv A j A (RingHom.id A))
      (hOpenInv_isIso A j A (RingHom.id A)) := Iso.ext ha
  have hh : a.hom = hOpen A j A (RingHom.id A) := congrArg Iso.inv hi
  rw [← hh]
  exact hg M W m

private theorem underlying_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : X.Etale)
    (m : F.obj.obj (op W)) :
    (((cUnderlying A X A (RingHom.id A)).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F)).hom.app
        (op ((toProEt X).obj W))) (siteSumUnitSection A X F W m) =
      (((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app F).hom.app (op W)) m := by
  exact ConcreteCategory.congr_hom
    (congrArg (fun z ↦ z.hom.app (op ((toProEt X).obj W)))
      ((cUnderlying A X A (RingHom.id A)).inv_hom_id_app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F)))
    ((((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app F).hom.app (op W)) m)

private theorem unit_map_section (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (f : F ⟶ G)
    (W : X.Etale) (m : F.obj.obj (op W)) :
    ((sitePull A X).map f).val.app (op ((toProEt X).obj W))
      (siteSumUnitSection A X F W m) =
      siteSumUnitSection A X G W (f.hom.app (op W) m) := by
  apply (ConcreteCategory.bijective_of_isIso
    (((cUnderlying A X A (RingHom.id A)).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj G)).hom.app
        (op ((toProEt X).obj W)))).1
  have hn := (cUnderlying A X A (RingHom.id A)).hom.naturality
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).map f)
  have hn' := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u + 1})
    (congrArg (fun z ↦ z.hom.app (op ((toProEt X).obj W))) hn)
    (siteSumUnitSection A X F W m)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    AddCommGrpCat.comp_apply] at hn'
  erw [hn']
  erw [underlying_unit, underlying_unit]
  exact (ConcreteCategory.congr_hom
    (congrArg (fun z ↦ z.hom.app (op W))
      ((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.naturality f)) m).symm

private theorem unit_restrict_section (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    {V W : X.Etale} (a : W ⟶ V) (m : F.obj.obj (op V)) :
    ((sitePull A X).obj F).val.presheaf.map ((toProEt X).map a).op
      (siteSumUnitSection A X F V m) =
      siteSumUnitSection A X F W (F.obj.map a.op m) := by
  apply (ConcreteCategory.bijective_of_isIso
    (((cUnderlying A X A (RingHom.id A)).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F)).hom.app
        (op ((toProEt X).obj W)))).1
  have hn := (((cUnderlying A X A (RingHom.id A)).hom.app
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj F)).hom).naturality
      (((toProEt X).map a).op)
  have hn' := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u + 1}) hn
    (siteSumUnitSection A X F V m)
  simp only [AddCommGrpCat.comp_apply] at hn'
  erw [hn', underlying_unit, underlying_unit]
  exact (ConcreteCategory.congr_hom (C := ModuleCat.{u + 1} A)
    (((comparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app F).hom.naturality
      a.op) m).symm

private theorem site_direct_unit (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] {Z T : Scheme.{u}} (g : Z ⟶ T)
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (V : T.Etale)
    (x : ((Etale.lowerStar (ModuleCat.{u + 1} A) g).obj F).obj.obj (op V)) :
    ((hDirect A g A (RingHom.id A)).app F).val.app (op ((toProEt T).obj V))
      (siteSumUnitSection A T ((Etale.lowerStar (ModuleCat.{u + 1} A) g).obj F) V x) =
      siteSumUnitSection A Z F
        ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V) x := by
  have hd := (Classical.choose_spec (cDirect_existsUnique A g A (RingHom.id A))).1
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj F)
    (op ((toProEt T).obj V))
  change ∀ m,
    (((cUnderlying A Z A (RingHom.id A)).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj F)).hom.app
        (op ((toProEt Z).obj ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V))))
      (((cDirect A g A (RingHom.id A)).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj F)).val.app
          (op ((toProEt T).obj V)) m) =
    (((cUnderlying A T A (RingHom.id A)).hom.app
      ((ProEtale.lowerStar (ModuleCat.{u + 1} A) g).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj F))).hom.app
          (op ((toProEt T).obj V))) m at hd
  have hm := NatTrans.congr_app (siteDirect_eq g A) F
  apply (ConcreteCategory.bijective_of_isIso
    (((cUnderlying A Z A (RingHom.id A)).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj F)).hom.app
        (op ((toProEt Z).obj
          ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V))))).1
  simp only [hDirect, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    SheafOfModules.id_val, PresheafOfModules.id_app,
    ConcreteCategory.comp_apply]
  erw [ConcreteCategory.id_apply, hd]
  have hn := (cUnderlying A T A (RingHom.id A)).hom.naturality
    ((lowerStarComparisonUpperStarBaseChange g (ModuleCat.{u + 1} A)).app F)
  have hnv := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u + 1})
    (congrArg (fun z ↦ z.hom.app (op ((toProEt T).obj V))) hn)
    (siteSumUnitSection A T ((Etale.lowerStar (ModuleCat.{u + 1} A) g).obj F) V x)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    AddCommGrpCat.comp_apply] at hnv
  erw [hm, hnv, underlying_unit, underlying_unit]
  have hi : (((lowerStarCompComparisonLowerStarIso g (ModuleCat.{u + 1} A)).inv.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj F)).hom.app (op V)) = 𝟙 _ := by
    simp only [Functor.comp_obj, lowerStarCompComparisonLowerStarIso,
      toProEtCompOverPullbackIso, Iso.trans_inv, Iso.symm_inv,
      Functor.sheafPushforwardContinuousIso_inv, Category.assoc, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
      Functor.sheafPushforwardContinuous_obj_obj_obj,
      Functor.sheafPushforwardContinuousComp_hom_app_hom_app, Functor.whiskerRight_app,
      Functor.op_obj, NatTrans.op_app, NatIso.ofComponents_hom_app, Iso.refl_hom, op_id,
      Functor.sheafPushforwardContinuousComp_inv_app_hom_app, Category.comp_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  have h := unit_app_comp_map_lowerStarComparisonUpperStarBaseChange_app
    (ModuleCat.{u + 1} A) g F
  have hv := congrArg (fun z ↦ z.hom.app (op V)) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Etale.lowerStar_map_hom_app, hi] at hv
  exact ConcreteCategory.congr_hom hv x

private theorem etale_clopen_ext {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology (Type (u + 1)))
    {V W C : X.Etale} (s : W ⟶ V) (t : C ⟶ V)
    [IsOpenImmersion s.left] [IsOpenImmersion t.left]
    (h : IsCompl (Set.range s.left) (Set.range t.left))
    {x y : G.obj.obj (op V)}
    (hs : G.obj.map s.op x = G.obj.map s.op y)
    (ht : G.obj.map t.op x = G.obj.map t.op y) : x = y := by
  have hh : TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ x) =
      TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ y) :=
    (Scheme.Etale.existsUnique_of_isCompl G s t h
      (TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ G.obj.map s.op x))
      (TypeCat.ofHom (fun _ : PUnit.{u + 2} ↦ G.obj.map t.op x))).unique
      ⟨rfl, rfl⟩ ⟨by ext _; exact hs.symm, by ext _; exact ht.symm⟩
  exact ConcreteCategory.congr_hom hh PUnit.unit

private theorem etale_normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] {U T : Scheme.{u}}
    (e : U ⟶ T) [Etale e] [IsSeparated e] (c : Compactification e)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (m : M.obj.obj (op W)) :
    (((Etale.compactificationSheafToDirectImage A c).app M).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
      ((((Etale.etaleCompactificationGraphMap A e c).app M).hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
        (etaleSumLiftGenerator A e M W m)) =
    (Scheme.Etale.graphExtend e M W) m := by
  have h := Etale.compactSupportGraphSheafComparison_normalization_transpose A e c M
  have h' := congrArg (fun z ↦ z.hom.app (op W)) h
  simp only [Adjunction.homEquiv_unit, Etale.etaleLowerShriekRestrictionAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    ObjectProperty.FullSubcategory.comp_hom, Etale.localizationRestriction_map_hom_app,
    Etale.lowerStarUnit_app_hom_app, Etale.localizationRestriction_obj_val_obj] at h'
  have hm := ConcreteCategory.congr_hom h' m
  dsimp only [etaleSumLiftGenerator, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, ModuleCat.comp_apply]
  exact hm

private theorem restrict_comp_apply (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    {B C D : X.Etale} (f : B ⟶ C) (g : C ⟶ D) (z : F.obj.obj (op D)) :
    F.obj.map f.op (F.obj.map g.op z) = F.obj.map (f ≫ g).op z := by
  exact (ConcreteCategory.congr_hom (F.obj.map_comp g.op f.op) z).symm

section EtaleGeometry

variable {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
  (c : Compactification e)
private def etGraphArrow (W : U.Etale) :
    (MorphismProperty.Over.map ⊤ (inferInstance : Etale c.i)).obj W ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ c.g).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 W.left) (W.hom ≫ c.i) (by
      change 𝟙 W.left ≫ (W.hom ≫ e) = (W.hom ≫ c.i) ≫ c.g
      simpa only [Category.id_comp, Category.assoc] using
        congrArg (fun f ↦ W.hom ≫ f) c.comm))
    (by simp) trivial

omit [IsSeparated e] in
private theorem etGraph_geometry (W : U.Etale) :
    Scheme.Etale.graph e W ≫
      (MorphismProperty.Over.pullbackComp c.i c.g e c.comm).hom.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) =
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ c.i inferInstance trivial).unit.app W ≫
        (MorphismProperty.Over.pullback @Etale ⊤ c.i).map (etGraphArrow e c W) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [etGraphArrow, Scheme.Etale.graph_left, MorphismProperty.Over.pullback_map_left,
        MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]
  · simp [etGraphArrow, Scheme.Etale.graph_left, MorphismProperty.Over.pullback_map_left,
      MorphismProperty.Over.pullbackComp_hom_app_left, Category.assoc]

private theorem graphExtend_zero (A : Type (u + 1)) [CommRing A]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W B : U.Etale)
    (a : B ⟶ Scheme.Etale.graphTarget e W)
    (ha : Set.range a.left ⊆ (Set.range (Scheme.Etale.graph e W).left)ᶜ)
    (m : M.obj.obj (op W)) :
    M.obj.map a.op ((Scheme.Etale.graphExtend e M W) m) = 0 := by
  let b : B ⟶ Scheme.Etale.graphComplObj e W :=
    MorphismProperty.Over.homMk
      (IsOpenImmersion.lift (Scheme.Etale.graphComplι e W).left a.left (by
        change Set.range a.left ⊆ Set.range (Scheme.Etale.graphCompl e W).ι
        rw [Scheme.Opens.range_ι]
        exact ha))
      (by
        change _ ≫ (Scheme.Etale.graphComplι e W).left ≫ _ = _
        rw [← Category.assoc, IsOpenImmersion.lift_fac, MorphismProperty.Over.w]) trivial
  have hb : b ≫ Scheme.Etale.graphComplι e W = a :=
    MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)
  rw [← hb, op_comp, Functor.map_comp]
  have h := ConcreteCategory.congr_hom (Scheme.Etale.graphExtend_graphComplι e M W) m
  change M.obj.map (Scheme.Etale.graphComplι e W).op
    ((Scheme.Etale.graphExtend e M W) m) = 0 at h
  simp only [ModuleCat.comp_apply, h, map_zero]

omit [Etale e] [IsSeparated e] in
private theorem lowerStar_injective (A : Type (u + 1)) [CommRing A]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (B : c.Z.Etale) :
    Function.Injective
      (((Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M).hom.app
        (op B)) := by
  have : Mono ((Etale.openImmersionLowerShriekToLowerStar
    (ModuleCat.{u + 1} A) c.i).app M) :=
      Etale.mono_openImmersionLowerShriekToLowerStar_app A c.i M
  let ev := sheafToPresheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (evaluation _ (ModuleCat.{u + 1} A)).obj (op B)
  exact (ModuleCat.mono_iff_injective _).1
    (Functor.map_mono ev ((Etale.openImmersionLowerShriekToLowerStar
      (ModuleCat.{u + 1} A) c.i).app M))

private theorem etale_image (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (m : M.obj.obj (op W)) :
    (((Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ c.g).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))))
      ((((Etale.etaleCompactificationGraphMap A e c).app M).hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
        (etaleSumLiftGenerator A e M W m)) =
    M.obj.map ((MorphismProperty.Over.pullbackComp c.i c.g e c.comm).inv.app
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)).op
      ((Scheme.Etale.graphExtend e M W) m) := by
  have hn := etale_normalized A e c M W m
  simp only [Etale.compactificationSheafToDirectImage, NatTrans.comp_app,
    Functor.whiskerRight_app, ObjectProperty.FullSubcategory.comp_hom,
    ModuleCat.comp_apply, Etale.lowerStar_map_hom_app,
    Etale.lowerStarComp_hom_app_hom_app] at hn
  have hn' := congrArg
    (fun z ↦ M.obj.map ((MorphismProperty.Over.pullbackComp c.i c.g e c.comm).inv.app
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)).op z) hn
  have hi (z : M.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ c.i).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ c.g).obj
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))))) :
      M.obj.map ((MorphismProperty.Over.pullbackComp c.i c.g e c.comm).inv.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)).op
      (M.obj.map ((MorphismProperty.Over.pullbackComp c.i c.g e c.comm).hom.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)).op z) = z := by
    have he : M.obj.map ((MorphismProperty.Over.pullbackComp c.i c.g e c.comm).hom.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)).op ≫
      M.obj.map ((MorphismProperty.Over.pullbackComp c.i c.g e c.comm).inv.app
        ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)).op = 𝟙 _ := by
      rw [← CategoryTheory.Functor.map_comp, ← op_comp, Iso.inv_hom_id_app, op_id,
        CategoryTheory.Functor.map_id]
    exact ConcreteCategory.congr_hom he z
  erw [hi] at hn'
  exact hn'

omit [Etale e] [IsSeparated e] in
private theorem openGenerator_inclusion (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (m : M.obj.obj (op W)) :
    M.obj.map (Scheme.Etale.graph c.i W).op
      ((((Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M).hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale c.i)).obj W)))
        (etaleSumLiftGenerator A c.i M W m)) = m := by
  let k := (Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M
  let r := Etale.upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) c.i
  have hu := Etale.unit_map_openImmersionLowerShriekToLowerStar_app_counit
    (ModuleCat.{u + 1} A) c.i M
  rw [Etale.openImmersionLowerShriekUpperStarAdjunction_unit_app,
    Etale.upperStarLowerStarAdjunction_counit_app_of_isOpenImmersion] at hu
  have hn := r.inv.naturality k
  simp only [Category.assoc] at hu
  erw [← reassoc_of% hn] at hu
  erw [Iso.inv_hom_id_app_assoc] at hu
  dsimp only [Etale.openImmersionRestriction,
    Etale.openImmersionRestrictionLowerStarAdjunction] at hu
  have hv := congrArg (fun z ↦ z.hom.app (op W)) hu
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Etale.localizationRestriction_map_hom_app,
    Etale.localizationRestrictionLowerStarAdjunction_counit_app_hom_app,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at hv
  have he :
      (Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        c.i inferInstance).unit.app M ≫
      (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A)
        c.i inferInstance).hom.app _ =
      (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) c.i).unit.app M := by
    simp only [Etale.etaleLowerShriekUpperStarAdjunction, Adjunction.ofNatIsoRight_unit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc,
      Iso.symm_hom]
    erw [Iso.inv_hom_id_app, Category.comp_id]
    rfl
  unfold etaleSumLiftGenerator
  rw [he]
  have hm := ConcreteCategory.congr_hom hv m
  exact hm

private theorem etale_graph_restriction (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (m : M.obj.obj (op W)) :
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M).obj.map
      (etGraphArrow e c W).op
      ((((Etale.etaleCompactificationGraphMap A e c).app M).hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
        (etaleSumLiftGenerator A e M W m)) =
      etaleSumLiftGenerator A c.i M W m := by
  apply lowerStar_injective e c A M
    ((MorphismProperty.Over.map ⊤ (inferInstance : Etale c.i)).obj W)
  let q := Scheme.Etale.graph c.i W
  have : IsIso q := by
    have hf : pullback.fst (W.hom ≫ c.i) c.i ≫ W.hom =
        pullback.snd (W.hom ≫ c.i) c.i := by
      apply (cancel_mono c.i).1
      simpa only [Category.assoc] using (pullback.condition (f := W.hom ≫ c.i) (g := c.i))
    let qi : Scheme.Etale.graphTarget c.i W ⟶ W :=
      MorphismProperty.Over.homMk (pullback.fst (W.hom ≫ c.i) c.i) hf trivial
    refine ⟨⟨qi, ?_, ?_⟩⟩
    · apply MorphismProperty.Over.Hom.ext
      simp [q, qi, Scheme.Etale.graph_left]
    · apply MorphismProperty.Over.Hom.ext
      apply pullback.hom_ext <;>
        simp [q, qi, Scheme.Etale.graph_left, Category.assoc, hf]
  apply (ConcreteCategory.bijective_of_isIso (M.obj.map q.op)).1
  let V := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W
  let pc := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) c.i c.g e c.comm
  have hg : q ≫ (MorphismProperty.Over.pullback @Etale ⊤ c.i).map
      (etGraphArrow e c W) ≫ pc.inv.app V = Scheme.Etale.graph e W := by
    have hh : Scheme.Etale.graph e W ≫ pc.hom.app V =
        q ≫ (MorphismProperty.Over.pullback @Etale ⊤ c.i).map (etGraphArrow e c W) :=
      etGraph_geometry e c W
    calc
      _ = (Scheme.Etale.graph e W ≫ pc.hom.app V) ≫ pc.inv.app V :=
        congrArg (fun f ↦ f ≫ pc.inv.app V) hh.symm
      _ = _ := by
        rw [Category.assoc, Iso.hom_inv_id_app]
        exact Category.comp_id _
  let k := (Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M
  have hn := ConcreteCategory.congr_hom (C := ModuleCat.{u + 1} A)
    (k.hom.naturality (etGraphArrow e c W).op)
    ((((Etale.etaleCompactificationGraphMap A e c).app M).hom.app (op V))
      (etaleSumLiftGenerator A e M W m))
  simp only [ModuleCat.comp_apply] at hn
  erw [hn, etale_image e c A M W m]
  erw [Etale.lowerStar_obj_val_map]
  erw [restrict_comp_apply, restrict_comp_apply, Category.assoc, hg]
  have hgm : M.obj.map (Scheme.Etale.graph e W).op
      ((Scheme.Etale.graphExtend e M W) m) = m :=
    ConcreteCategory.congr_hom (Scheme.Etale.graphExtend_graph e M W) m
  erw [hgm]
  exact (openGenerator_inclusion e c A M W m).symm

set_option maxHeartbeats 1000000 in
-- The iterated pullback objects have several equivalent site presentations;
-- elaborating their section maps needs more than the default heartbeat budget.
private theorem etale_complement_restriction (A : Type (u + 1)) [CommRing A]
    [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (m : M.obj.obj (op W)) (B : c.Z.Etale)
    (a : B ⟶ (MorphismProperty.Over.pullback @Etale ⊤ c.g).obj
      ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
    (ha : Set.range a.left ⊆ (Set.range (etGraphArrow e c W).left)ᶜ) :
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M).obj.map a.op
      ((((Etale.etaleCompactificationGraphMap A e c).app M).hom.app
        (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
        (etaleSumLiftGenerator A e M W m)) = 0 := by
  apply lowerStar_injective e c A M B
  let V := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W
  let P := (MorphismProperty.Over.pullback @Etale ⊤ c.g).obj V
  let pc := MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) c.i c.g e c.comm
  let q := Scheme.Etale.graph c.i W
  let r := (MorphismProperty.Over.pullback @Etale ⊤ c.i).map a ≫ pc.inv.app V
  let k : (Scheme.Etale.graphTarget e W).left ⟶ P.left :=
    (pc.hom.app V).left ≫ pullback.fst P.hom c.i
  have hk : (Scheme.Etale.graph e W).left ≫ k = (etGraphArrow e c W).left := by
    have h := congrArg (fun z ↦ z.left ≫ pullback.fst P.hom c.i)
      (etGraph_geometry e c W)
    change (Scheme.Etale.graph e W).left ≫ k =
      (Scheme.Etale.graph c.i W).left ≫
        ((MorphismProperty.Over.pullback @Etale ⊤ c.i).map (etGraphArrow e c W)).left ≫
          pullback.fst P.hom c.i at h
    erw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst] at h
    have hc := Scheme.Etale.graph_left_fst c.i W
    exact h.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ (etGraphArrow e c W).left) hc).trans (Category.id_comp _)))
  have hr : r.left ≫ k = pullback.fst B.hom c.i ≫ a.left := by
    change (((MorphismProperty.Over.pullback @Etale ⊤ c.i).map a ≫
      pc.inv.app V ≫ pc.hom.app V).left ≫ pullback.fst P.hom c.i) = _
    erw [Iso.inv_hom_id_app, Category.comp_id]
    exact pullback.lift_fst _ _ _
  have hd : Set.range r.left ⊆ (Set.range (Scheme.Etale.graph e W).left)ᶜ := by
    rintro _ ⟨z, rfl⟩ ⟨w, hw⟩
    apply ha ⟨pullback.fst B.hom c.i z, rfl⟩
    refine ⟨w, ?_⟩
    calc
      (etGraphArrow e c W).left w = k ((Scheme.Etale.graph e W).left w) := by
        exact congrArg (fun f ↦ f w) hk.symm
      _ = k (r.left z) := congrArg k hw
      _ = a.left (pullback.fst B.hom c.i z) := by
        exact congrArg (fun f ↦ f z) hr
  let l := (Etale.openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app M
  have hn := ConcreteCategory.congr_hom (C := ModuleCat.{u + 1} A)
    (l.hom.naturality a.op)
    ((((Etale.etaleCompactificationGraphMap A e c).app M).hom.app (op V))
      (etaleSumLiftGenerator A e M W m))
  simp only [ModuleCat.comp_apply] at hn
  erw [hn, etale_image e c A M W m]
  erw [Etale.lowerStar_obj_val_map]
  erw [restrict_comp_apply]
  simp only [map_zero]
  exact graphExtend_zero e A M W _ r hd m

end EtaleGeometry

/-- The generator-normalized sum comparison intertwines the two ordinary graph maps.
Here `hDirect` is the canonical ordinary direct-image mate and `hOpen` is the
canonical open-extension comparison, expressed in intrinsic constant-ring modules.
Source: finite_normalization proof, step 2; Stacks 0F4L, 09A5 and 09AF;
current blueprint Local pairs (blueprint: lem-sp-graph-map-site-square).

Proof:
1. Use the site-comparison adjunction to reduce equality of maps from the comparison
pullback to equality on etale sections. Sum extension is sheafification of the direct
sum over lifts, so it suffices to check each lift generator.
2. By lem-sp-site-sum-generator-normalization the left composite sends the generator
of (W,m) to the pro-etale generator of (W,eta(m)). The characterization of the
single-ring graph map gives the pro-etale open unit on the graph and zero on its
complement (lem-route-graph-map-exists-unique at one constant-ring level).
3. The etale graph comparison gives the etale open unit on the same clopen graph
and zero on its complement, by the graph construction and its transpose normalization
(lem-asd-compact-support-graph-sheaf-normalization and its transpose), using that the
open inclusion i_! -> i_* is sectionwise injective (lem-amb-unbounded-proper-open-pasting).
The direct-image mate sends eta(x) to eta(x) on the base-changed object by the upstream
mate-unit identity (LowerStarCoherence), and the open comparison sends the etale open
unit to the pro-etale open unit by lem-sp-site-sum-generator-normalization specialized
to the open immersion i. Naturality preserves the zero restriction on the open
complement of the graph. The graph and its open complement are complementary etale
pieces, so the two-piece uniqueness of the etale restriction of the target sheaf
gives equality.
4. Equality on every lift generator gives the asserted equality for every M by step 1.
-/
theorem graphMap_site_square (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    [QuasiCompact c.i] (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (@asIso _ _ _ _ (siteSumInv A e) (siteSumInv_isIso A e)).inv.app M ≫
        (levelGraphMap A e c).app ((sitePull A U).obj M) =
      (sitePull A T).map ((Etale.etaleCompactificationGraphMap A e c).app M) ≫
        (StrictTower.hDirect A c.g A (RingHom.id A)).app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M) ≫
        (StrictTower.moduleDirectImage A c.g).map
          ((StrictTower.hOpen A c.i A (RingHom.id A)).app M) := by
  apply comparison_sum_hom_ext A e M
  intro W m
  let V := (MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W
  let P := (MorphismProperty.Over.pullback @Etale ⊤ c.g).obj V
  let F := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).obj M
  let N := (sitePull A U).obj M
  let R := (moduleJ A c.i).obj N
  let ξ := etaleSumLiftGenerator A e M W m
  let x := ((Etale.etaleCompactificationGraphMap A e c).app M).hom.app (op V) ξ
  let x' := ((levelGraphMap A e c).app N).val.app (op ((toProEt T).obj V))
    (levelGenerator A e N ((toProEt U).obj W) (siteSumUnitSection A U M W m))
  let y := ((hOpen A c.i A (RingHom.id A)).app M).val.app (op ((toProEt c.Z).obj P))
    (siteSumUnitSection A c.Z F P x)
  change ((levelGraphMap A e c).app N).val.app (op ((toProEt T).obj V))
      (((@asIso _ _ _ _ (siteSumInv A e) (siteSumInv_isIso A e)).inv.app M).val.app
        (op ((toProEt T).obj V))
        (siteSumUnitSection A T
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) V ξ)) =
    ((hOpen A c.i A (RingHom.id A)).app M).val.app (op ((toProEt c.Z).obj P))
      (((hDirect A c.g A (RingHom.id A)).app F).val.app (op ((toProEt T).obj V))
        (((sitePull A T).map ((Etale.etaleCompactificationGraphMap A e c).app M)).val.app
          (op ((toProEt T).obj V))
          (siteSumUnitSection A T
            ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) V ξ)))
  erw [site_sum_generator A e M W m, unit_map_section,
    site_direct_unit A c.g F V x]
  change x' = y
  let s := etGraphArrow e c W
  have hsopen : IsOpenImmersion s.left :=
    (graph_clopen c ((toProEt T).obj V) W.hom rfl).1
  have hsclosed : IsClosedImmersion s.left :=
    (graph_clopen c ((toProEt T).obj V) W.hom rfl).2
  let C : P.left.Opens :=
    ⟨(Set.range s.left)ᶜ, s.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let B : c.Z.Etale := Scheme.Etale.mk (C.ι ≫ P.hom)
  let t : B ⟶ P := MorphismProperty.Over.homMk C.ι rfl trivial
  have : IsOpenImmersion t.left := (inferInstance : IsOpenImmersion C.ι)
  have hcompl : IsCompl (Set.range s.left) (Set.range t.left) := by
    change IsCompl (Set.range s.left) (Set.range C.ι)
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  have ht : Set.range t.left ⊆ (Set.range s.left)ᶜ := by
    change Set.range C.ι ⊆ (Set.range s.left)ᶜ
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.refl _
  let G := (comparisonLowerStar (Type (u + 1)) c.Z).obj
    ((sheafCompose (Scheme.ProEt.topology c.Z) (forget (ModuleCat.{u + 1} A))).obj
      ((fixedRestriction A c.Z).obj R))
  have hγ := (levelGraphMap_existsUnique A e c).exists.choose_spec N
    ((toProEt U).obj W) (siteSumUnitSection A U M W m)
  apply etale_clopen_ext G s t hcompl
  · have hx : R.val.presheaf.map ((toProEt c.Z).map s).op x' =
        levelGenerator A c.i N ((toProEt U).obj W)
          (siteSumUnitSection A U M W m) := hγ.1
    have hy : R.val.presheaf.map ((toProEt c.Z).map s).op y =
        levelGenerator A c.i N ((toProEt U).obj W)
          (siteSumUnitSection A U M W m) := by
      dsimp only [y]
      erw [← PresheafOfModules.naturality_apply, unit_restrict_section,
        etale_graph_restriction e c A M W m, site_open_generator A c.i M W m]
    exact hx.trans hy.symm
  · have hx : R.val.presheaf.map ((toProEt c.Z).map t).op x' = 0 :=
      hγ.2 ((toProEt c.Z).obj B) ((toProEt c.Z).map t) ht
    have hy : R.val.presheaf.map ((toProEt c.Z).map t).op y = 0 := by
      dsimp only [y]
      erw [← PresheafOfModules.naturality_apply, unit_restrict_section,
        etale_complement_restriction e c A M W m B t ht]
      simp only [siteSumUnitSection, map_zero]
    exact hx.trans hy.symm

end AlgebraicGeometry.ProEtale.VaryingRingGraph
