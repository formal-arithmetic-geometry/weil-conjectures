/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.ExtendedCochainTruncationTower
public import Sheaf.CategoryTheory.MapGoodUpperTruncation
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! Left exact functors commute naturally with the entire upper smart truncation tower.
Source: Stacks Project, Tags 0118, 0156 and 015X.
(blueprint: lem-sp-extended-smart-truncation-map-iso).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T]

/-- The left exact comparison at each extended cutoff, including both endpoints. -/
noncomputable def extendedTruncationMapStepIso (K : CochainComplex C ℤ) (a : EInt) :
    (T.mapHomologicalComplex (.up ℤ)).obj (K.extendedTruncationTower.obj a) ≅
      (extendedTruncationTower ((T.mapHomologicalComplex (.up ℤ)).obj K)).obj a := by
  induction a using WithBotTop.rec with
  | bot =>
    exact ((T.mapHomologicalComplex (.up ℤ)).map_isZero (isZero_zero _)).iso (isZero_zero _)
  | coe a => exact asIso (mapTruncLEComparison T K (a - 1))
  | top => exact Iso.refl _

@[reassoc]
theorem extendedTruncationMapStepIso_hom_ι (K : CochainComplex C ℤ) (a : EInt) :
    (extendedTruncationMapStepIso T K a).hom ≫
        (extendedTruncationTowerι ((T.mapHomologicalComplex (.up ℤ)).obj K)).app a =
      (T.mapHomologicalComplex (.up ℤ)).map (K.extendedTruncationTowerι.app a) := by
  induction a using WithBotTop.rec with
  | bot =>
    exact ((T.mapHomologicalComplex (.up ℤ)).map_isZero
      (isZero_zero _)).eq_of_src _ _
  | coe a => exact mapTruncLEComparison_ι T K (a - 1)
  | top =>
    change 𝟙 _ ≫ 𝟙 _ = (T.mapHomologicalComplex (.up ℤ)).map (𝟙 K)
    rw [Category.id_comp, CategoryTheory.Functor.map_id]

/-- The inclusion-normalized step isomorphisms commute with all cutoff maps. -/
noncomputable def extendedTruncationMapIso (K : CochainComplex C ℤ) :
    K.extendedTruncationTower ⋙ T.mapHomologicalComplex (.up ℤ) ≅
      (extendedTruncationTower ((T.mapHomologicalComplex (.up ℤ)).obj K)) :=
  NatIso.ofComponents (extendedTruncationMapStepIso T K) (by
    intro a b f
    apply (cancel_mono
      ((extendedTruncationTowerι ((T.mapHomologicalComplex (.up ℤ)).obj K)).app b)).1
    change ((T.mapHomologicalComplex (.up ℤ)).map (K.extendedTruncationTower.map f) ≫
      (extendedTruncationMapStepIso T K b).hom) ≫ _ =
        ((extendedTruncationMapStepIso T K a).hom ≫
          (extendedTruncationTower ((T.mapHomologicalComplex (.up ℤ)).obj K)).map f) ≫ _
    rw [Category.assoc, extendedTruncationMapStepIso_hom_ι,
      ← CategoryTheory.Functor.map_comp, extendedTruncationTower_map_ι, Category.assoc,
      extendedTruncationTower_map_ι, extendedTruncationMapStepIso_hom_ι])

/-- The tower comparison is natural in maps of the original complexes. -/
theorem extendedTruncationMapIso_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    Functor.whiskerRight (extendedTruncationTowerMap f) (T.mapHomologicalComplex (.up ℤ)) ≫
        (extendedTruncationMapIso T L).hom =
      (extendedTruncationMapIso T K).hom ≫
        extendedTruncationTowerMap ((T.mapHomologicalComplex (.up ℤ)).map f) := by
  apply NatTrans.ext
  funext a
  apply (cancel_mono
    ((extendedTruncationTowerι ((T.mapHomologicalComplex (.up ℤ)).obj L)).app a)).1
  change ((T.mapHomologicalComplex (.up ℤ)).map ((extendedTruncationTowerMap f).app a) ≫
      (extendedTruncationMapStepIso T L a).hom) ≫ _ =
    ((extendedTruncationMapStepIso T K a).hom ≫
      (extendedTruncationTowerMap ((T.mapHomologicalComplex (.up ℤ)).map f)).app a) ≫ _
  rw [Category.assoc, extendedTruncationMapStepIso_hom_ι, ← CategoryTheory.Functor.map_comp,
    extendedTruncationTowerMap_app_ι, Category.assoc, extendedTruncationTowerMap_app_ι,
    ← Category.assoc, extendedTruncationMapStepIso_hom_ι, CategoryTheory.Functor.map_comp]

end CochainComplex
