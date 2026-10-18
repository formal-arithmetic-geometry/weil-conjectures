/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.ExtendedCochainTruncationTower
public import Sheaf.CategoryTheory.DoubleComplexTruncationDecalage
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplex

/-! Smart horizontal truncations and the entire decalage tower.
Source: Stacks Project, Tags 0118, 0156 and 015X.
(blueprint: lem-sp-smart-truncation-decalage-tower).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/-- Totalize all horizontal upper truncations, extending by zero and the full total. -/
noncomputable def smartTruncationTower (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) :
    EInt ⥤ CochainComplex C ℤ :=
  (CochainComplex.extendedTruncationTower J) ⋙ totalFunctor C (.up ℤ) (.up ℤ) (.up ℤ)

/-- The inclusion of each smart-truncation total into the full total. -/
noncomputable def smartTruncationTowerι (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) :
    J.smartTruncationTower ⟶ (Functor.const EInt).obj (J.total (.up ℤ)) where
  app a := total.map ((CochainComplex.extendedTruncationTowerι J).app a) (.up ℤ)
  naturality a b f := by
    change total.map ((CochainComplex.extendedTruncationTower J).map f) (.up ℤ) ≫
        total.map ((CochainComplex.extendedTruncationTowerι J).app b) (.up ℤ) =
      total.map ((CochainComplex.extendedTruncationTowerι J).app a) (.up ℤ) ≫ 𝟙 _
    rw [← total.map_comp, CochainComplex.extendedTruncationTower_map_ι]
    exact (Category.comp_id _).symm

/-- Bicomplex maps act on all horizontal smart-truncation totals. -/
noncomputable def smartTruncationTowerMap
    {J J' : HomologicalComplex₂ C (.up ℤ) (.up ℤ)} (f : J ⟶ J') :
    J.smartTruncationTower ⟶ J'.smartTruncationTower :=
  Functor.whiskerRight (CochainComplex.extendedTruncationTowerMap f)
    (totalFunctor C (.up ℤ) (.up ℤ) (.up ℤ))

theorem smartTruncationTower_bot_isZero
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) :
    IsZero (J.smartTruncationTower.obj ⊥) :=
  total.isZero (0 : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) (.up ℤ) (isZero_zero _)

/-- The normalized identification of each total smart cut with its decalage step. -/
noncomputable def smartTruncationDecalageStepIso
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (a : EInt) : J.smartTruncationTower.obj a ≅ L.decalageTower.obj a := by
  induction a using WithBotTop.rec with
  | bot =>
    exact (smartTruncationTower_bot_isZero J).iso
      (IsZero.of_mono_eq_zero (⊥ : Subobject (J.total (.up ℤ))).arrow Subobject.bot_arrow)
  | coe a =>
    letI := J.totalTruncLEToDecalage_isIso hJ L hL (a - 1)
    change HomologicalComplex₂.total (CochainComplex.truncLE J (a - 1)) (.up ℤ) ≅
      (L.decalage.step (1 - a) : CochainComplex C ℤ)
    exact asIso (J.totalTruncLEToDecalage hJ L hL (a - 1)) ≪≫
      eqToIso (congrArg (fun q : ℤ ↦ (L.decalage.step q : CochainComplex C ℤ)) (by omega))
  | top => exact (asIso ((⊤ : Subobject (J.total (.up ℤ))).arrow)).symm

@[reassoc]
theorem smartTruncationDecalageStepIso_hom_arrow
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (a : EInt) :
    (J.smartTruncationDecalageStepIso hJ L hL a).hom ≫
        (L.decalageTowerStep a).arrow = J.smartTruncationTowerι.app a := by
  induction a using WithBotTop.rec with
  | bot => exact (smartTruncationTower_bot_isZero J).eq_of_src _ _
  | coe a =>
    have cast_arrow {q r : ℤ} (h : q = r) :
        eqToHom (congrArg (fun z : ℤ ↦ (L.decalage.step z : CochainComplex C ℤ)) h) ≫
          (L.decalage.step r).arrow = (L.decalage.step q).arrow := by
      subst r
      exact Category.id_comp _
    change (J.totalTruncLEToDecalage hJ L hL (a - 1) ≫
      eqToHom (congrArg (fun q : ℤ ↦ (L.decalage.step q : CochainComplex C ℤ))
        (show -(a - 1) = 1 - a by omega))) ≫ (L.decalage.step (1 - a)).arrow =
        total.map (CochainComplex.ιTruncLE J (a - 1)) (.up ℤ)
    rw [Category.assoc, cast_arrow (show -(a - 1) = 1 - a by omega)]
    exact J.totalTruncLEToDecalage_arrow hJ L hL (a - 1)
  | top =>
    change inv ((⊤ : Subobject (J.total (.up ℤ))).arrow) ≫
      (⊤ : Subobject (J.total (.up ℤ))).arrow = total.map (𝟙 J) (.up ℤ)
    rw [IsIso.inv_hom_id, total.map_id]

/-- The entire smart-truncation tower identifies with the decalage tower. -/
noncomputable def smartTruncationDecalageTowerIso
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p) :
    J.smartTruncationTower ≅ L.decalageTower :=
  NatIso.ofComponents (J.smartTruncationDecalageStepIso hJ L hL) (by
    intro a b f
    apply (cancel_mono (L.decalageTowerStep b).arrow).1
    change (J.smartTruncationTower.map f ≫
        (J.smartTruncationDecalageStepIso hJ L hL b).hom) ≫ _ =
      ((J.smartTruncationDecalageStepIso hJ L hL a).hom ≫
        Subobject.ofLE _ _ (L.decalageTowerStep_monotone (leOfHom f))) ≫ _
    rw [Category.assoc, smartTruncationDecalageStepIso_hom_arrow,
      Category.assoc, Subobject.ofLE_arrow, smartTruncationDecalageStepIso_hom_arrow]
    have h := J.smartTruncationTowerι.naturality f
    change J.smartTruncationTower.map f ≫ J.smartTruncationTowerι.app b =
      J.smartTruncationTowerι.app a ≫ 𝟙 _ at h
    exact h.trans (Category.comp_id _))

@[reassoc]
theorem smartTruncationTowerMap_app_ι
    {J J' : HomologicalComplex₂ C (.up ℤ) (.up ℤ)} (f : J ⟶ J') (a : EInt) :
    (smartTruncationTowerMap f).app a ≫ J'.smartTruncationTowerι.app a =
      J.smartTruncationTowerι.app a ≫ total.map f (.up ℤ) := by
  change total.map ((CochainComplex.extendedTruncationTowerMap f).app a) (.up ℤ) ≫
      total.map ((CochainComplex.extendedTruncationTowerι J').app a) (.up ℤ) =
    total.map ((CochainComplex.extendedTruncationTowerι J).app a) (.up ℤ) ≫ total.map f (.up ℤ)
  rw [← total.map_comp, ← total.map_comp]
  exact congrArg (fun u ↦ total.map u (.up ℤ))
    (CochainComplex.extendedTruncationTowerMap_app_ι f a)

/-- Monic inclusions force the tower identification to commute with comparison maps. -/
theorem smartTruncationDecalageTowerIso_naturality
    {J J' : HomologicalComplex₂ C (.up ℤ) (.up ℤ)} (f : J ⟶ J')
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (hJ' : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J'.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (L' : DecreasingFiltration (J'.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p)
    (hL' : ∀ p n : ℤ, L'.complexStep p n = (J'.secondFiltration n).step p)
    (t : (⟨J.total (.up ℤ), L⟩ : FilteredObject (CochainComplex C ℤ)) ⟶
      (⟨J'.total (.up ℤ), L'⟩ : FilteredObject (CochainComplex C ℤ)))
    (ht : t.hom = total.map f (.up ℤ)) :
    smartTruncationTowerMap f ≫ (J'.smartTruncationDecalageTowerIso hJ' L' hL').hom =
      (J.smartTruncationDecalageTowerIso hJ L hL).hom ≫
        DecreasingFiltration.decalageTowerMap t := by
  apply NatTrans.ext
  funext a
  apply (cancel_mono (L'.decalageTowerStep a).arrow).1
  change ((smartTruncationTowerMap f).app a ≫
      (J'.smartTruncationDecalageStepIso hJ' L' hL' a).hom) ≫ _ =
    ((J.smartTruncationDecalageStepIso hJ L hL a).hom ≫
      (DecreasingFiltration.decalageTowerMap t).app a) ≫ _
  have hd := DecreasingFiltration.decalageTowerMap_app_arrow t a
  change (DecreasingFiltration.decalageTowerMap t).app a ≫
    (L'.decalageTowerStep a).arrow = (L.decalageTowerStep a).arrow ≫ t.hom at hd
  rw [Category.assoc, smartTruncationDecalageStepIso_hom_arrow,
    Category.assoc, hd, ← Category.assoc, smartTruncationDecalageStepIso_hom_arrow,
    ht, smartTruncationTowerMap_app_ι]

end HomologicalComplex₂

namespace CategoryTheory
variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The spectral object of all mapping cones of a cochain tower. -/
noncomputable def cochainTowerSpectralObjectFunctor :
    (EInt ⥤ CochainComplex C ℤ) ⥤ Abelian.SpectralObject C EInt :=
  (HomotopyCategory.spectralObjectMappingCone C).precompFunctor ⋙
    (HomotopyCategory.homologyFunctor C (.up ℤ) 0).mapHomologicalSpectralObject EInt

end CategoryTheory

namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/-- The tower identification identifies all interval cones and their connecting maps. -/
noncomputable def smartTruncationDecalageSpectralObjectIso
    (J : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hJ : ∀ i j : ℤ, i < 0 ∨ j < 0 → IsZero ((J.X i).X j))
    (L : DecreasingFiltration (J.total (.up ℤ)))
    (hL : ∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p) :
    (cochainTowerSpectralObjectFunctor C).obj J.smartTruncationTower ≅
      (filteredComplexDecalageSpectralObjectFunctor C).obj
        (⟨J.total (.up ℤ), L⟩ : FilteredObject (CochainComplex C ℤ)) :=
  (cochainTowerSpectralObjectFunctor C).mapIso (J.smartTruncationDecalageTowerIso hJ L hL)

end HomologicalComplex₂
