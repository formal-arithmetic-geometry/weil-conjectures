/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeMapNaturality

public import Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence
import Sheaf.AlgebraicGeometry.CartesianChartDiagramMap

/-! # Chart lifts commute with stage transitions

Source: Stacks Project, Tags 0EYM, 03CB and 03Q8.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale


open CartesianChartLiftNaturality
attribute [local irreducible] restrictedOverCohomologyMap
  cartesianDerivedImageMap cartesianChartCohomologyLift upperStar upperStarCompDerivedPlus
  cartesianChartRawAdjunctionIso rawRestrictedCohomologyComparison
set_option backward.isDefEq.respectTransparency true
namespace CartesianChartLiftNaturality
attribute [local instance] isIso_rawRestrictedCohomologyComparison

theorem chart_inverse_comparison_map
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (j : I) (W : (D.obj j).left.Etale) (V : c.pt.left.Etale)
    (r : V.left ⟶ W.left)
    (hr : IsPullback r V.hom W.hom (c.π.app j).left)
    (l m : Over j) (a : m ⟶ l)
    (x : restrictedOverCohomology (pullback.snd f (D.obj j).hom)
      (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D j).obj l) W)
    (hl2 : (show pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map
      l.hom).left (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map a).left)
      ≫ pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) =
      pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom))
    (hw : (show pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map
      l.hom).left (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map a).left)
      ≫ (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
      j).hom)) =
      pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
        j).hom)) :
    letI := isIso_rawRestrictedCohomologyComparison (pullback.snd (D.map l.hom).left (pullback.snd
      f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map l.hom).left
      (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
      j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W
    letI := isIso_rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left (pullback.snd
      f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map m.hom).left
      (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
      j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W
    ((asIso (rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left (pullback.snd f
      (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map m.hom).left
      (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
      j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv (restrictedOverCohomologyMap (pullback.snd
      f (D.obj j).hom) (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F) (q : ℤ)
      ((cartesianChartDiagram f D j).map a) W x)) = abelianHigherDirectImageRawPullback (show
      pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map l.hom).left
      (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map a).left)
      (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
        j).hom))
      (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
        j).hom)) hw q
      (((pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u +
        1}]).obj (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      (((pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u +
        1}]).obj (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      ((upperStarComp AddCommGrpCat.{u + 1} (show pullback (D.map m.hom).left (pullback.snd f
        (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
        ((cartesianChartDiagram f D j).map a).left)
        (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom))
        (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom)) hl2.symm).inv.app
          (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W ((asIso
          (rawRestrictedCohomologyComparison (pullback.snd (D.map l.hom).left (pullback.snd f
          (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map l.hom).left
          (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
          j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv x) := by
  have _ := hr
  have hBl_hom : ((cartesianChartDiagram f D j).obj l).hom = pullback.snd (D.map l.hom).left
    (pullback.snd f (D.obj j).hom) := by
    exact chartDiagram_obj_hom f D j l
  have hBm_hom : ((cartesianChartDiagram f D j).obj m).hom = pullback.snd (D.map m.hom).left
    (pullback.snd f (D.obj j).hom) := by
    exact chartDiagram_obj_hom f D j m
  let := isIso_rawRestrictedCohomologyComparison (pullback.snd (D.map l.hom).left (pullback.snd f
    (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map l.hom).left
    (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
    j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W
  let := isIso_rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left (pullback.snd f
    (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map m.hom).left
    (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
    j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W
  have hraw := restrictedOverCohomologyMap_raw_naturality_canonical
    (pullback.snd f (D.obj j).hom)
    (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
    q ((cartesianChartDiagram f D j).map a) W (by
      rw [← Category.assoc, Over.w]) x
  have hl1 : (show pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map
    l.hom).left (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map a).left) ≫
    pullback.fst (D.map l.hom).left (pullback.snd f (D.obj j).hom) =
      pullback.fst (D.map m.hom).left (pullback.snd f (D.obj j).hom) ≫ (D.map a.left).left := by
    rw [chartDiagram_map_left f D j l m a]
    exact pullback.lift_fst _ _ _
  have hl2 : (show pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map
    l.hom).left (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map a).left) ≫
    pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) =
      pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom) := by
    rw [chartDiagram_map_left f D j l m a]
    exact pullback.lift_snd _ _ _
  have hwh : (show pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map
    l.hom).left (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map a).left) ≫
    (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
    j).hom)) = (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f
    (D.obj j).hom)) := by
    dsimp only 
    change (show pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map
      l.hom).left (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map a).left)
      ≫ (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
      j).hom)) =
      pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
        j).hom)
    rw [← Category.assoc, hl2]
  have hcomp_eq : ((cartesianChartDiagram f D j).obj m).hom = (show pullback (D.map m.hom).left
    (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom)
    from ((cartesianChartDiagram f D j).map a).left) ≫ ((cartesianChartDiagram f D j).obj l).hom
    := by
    rw [hBm_hom, hBl_hom]
    exact hl2.symm
  have hraw' : rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left (pullback.snd f
    (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map m.hom).left
    (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
    j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W
      (abelianHigherDirectImageRawPullback (show pullback (D.map m.hom).left (pullback.snd f
        (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
        ((cartesianChartDiagram f D j).map a).left) (pullback.snd (D.map l.hom).left (pullback.snd
        f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) (pullback.snd (D.map m.hom).left
        (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) hwh q (((pullback.snd
        (D.map l.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) (((pullback.snd (D.map
        m.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst
        f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
        ((upperStarComp AddCommGrpCat.{u + 1} (show pullback (D.map m.hom).left (pullback.snd f
          (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
          ((cartesianChartDiagram f D j).map a).left)
          ((cartesianChartDiagram f D j).obj l).hom ((cartesianChartDiagram f D j).obj m).hom
            hcomp_eq).inv.app (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W
            ((asIso (rawRestrictedCohomologyComparison (pullback.snd (D.map l.hom).left
            (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd
            (D.map l.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj
            (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv x)) =
      (restrictedOverCohomologyMap (pullback.snd f (D.obj j).hom)
        (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F) (q : ℤ)
          ((cartesianChartDiagram f D j).map a) W x) := by
    have hraw0 := hraw.symm
    simp only [restrictedOverCoefficient] at hraw0
    change rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left (pullback.snd f
      (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map m.hom).left
      (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
      j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W
        (abelianHigherDirectImageRawPullback (show pullback (D.map m.hom).left (pullback.snd f
          (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
          ((cartesianChartDiagram f D j).map a).left) (pullback.snd (D.map l.hom).left
          (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) (pullback.snd (D.map
          m.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) hwh q
          (((pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u +
          1}]).obj (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
          (((pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u +
          1}]).obj (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
          ((upperStarComp AddCommGrpCat.{u + 1} (show pullback (D.map m.hom).left (pullback.snd f
            (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
            ((cartesianChartDiagram f D j).map a).left)
            ((cartesianChartDiagram f D j).obj l).hom ((cartesianChartDiagram f D j).obj m).hom
              hcomp_eq).inv.app (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
              W ((asIso (rawRestrictedCohomologyComparison (pullback.snd (D.map l.hom).left
              (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd
              (D.map l.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj
              (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv x)) = _
              at hraw0
    simpa only [hBl_hom, hBm_hom] using hraw0
  have hz' : ((asIso (rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left
    (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map
    m.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f
    (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv (restrictedOverCohomologyMap
    (pullback.snd f (D.obj j).hom) (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj
    F) (q : ℤ) ((cartesianChartDiagram f D j).map a) W x)) = abelianHigherDirectImageRawPullback
      (show pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map
        l.hom).left (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map
        a).left) (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f
        (D.obj j).hom)) (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom) ≫
        (pullback.snd f (D.obj j).hom)) hwh q (((pullback.snd (D.map l.hom).left (pullback.snd f
        (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
        j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) (((pullback.snd (D.map m.hom).left (pullback.snd
        f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
        j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      ((upperStarComp AddCommGrpCat.{u + 1} (show pullback (D.map m.hom).left (pullback.snd f
        (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
        ((cartesianChartDiagram f D j).map a).left)
        ((cartesianChartDiagram f D j).obj l).hom ((cartesianChartDiagram f D j).obj m).hom
          hcomp_eq).inv.app
        (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W ((asIso
          (rawRestrictedCohomologyComparison (pullback.snd (D.map l.hom).left (pullback.snd f
          (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map l.hom).left
          (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
          j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv x) := by
    dsimp only 
    exact (congrArg (fun y ↦ (asIso
      (rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj
        j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map m.hom).left
        (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
        j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv y) hraw'.symm).trans
      (Iso.hom_inv_id_apply (asIso
        (rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj
          j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map m.hom).left
          (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
          j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)) _)
  have hw : (show pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map
    l.hom).left (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map a).left) ≫
    (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
    j).hom)) =
      pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
        j).hom) := by
    rw [← Category.assoc, hl2]
  have hz'' : ((asIso (rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left
    (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map
    m.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f
    (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv (restrictedOverCohomologyMap
    (pullback.snd f (D.obj j).hom) (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj
    F) (q : ℤ) ((cartesianChartDiagram f D j).map a) W x)) = abelianHigherDirectImageRawPullback
    (show pullback (D.map m.hom).left (pullback.snd f (D.obj j).hom) ⟶ pullback (D.map l.hom).left
    (pullback.snd f (D.obj j).hom) from ((cartesianChartDiagram f D j).map a).left)
      (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
        j).hom))
      (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
        j).hom)) hw q
      (((pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u +
        1}]).obj (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      (((pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u +
        1}]).obj (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      ((upperStarComp AddCommGrpCat.{u + 1} (show pullback (D.map m.hom).left (pullback.snd f
        (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
        ((cartesianChartDiagram f D j).map a).left)
        (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom))
        (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom)) hl2.symm).inv.app
          (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W ((asIso
          (rawRestrictedCohomologyComparison (pullback.snd (D.map l.hom).left (pullback.snd f
          (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map l.hom).left
          (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
          j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv x) := by
    have hz0 := hz'
    change ((asIso (rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left
      (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map
      m.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f
      (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv (restrictedOverCohomologyMap
      (pullback.snd f (D.obj j).hom) (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u +
      1}]).obj F) (q : ℤ) ((cartesianChartDiagram f D j).map a) W x)) =
      abelianHigherDirectImageRawPullback (show pullback (D.map m.hom).left (pullback.snd f (D.obj
      j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
      ((cartesianChartDiagram f D j).map a).left)
        (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
          j).hom))
        (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom) ≫ (pullback.snd f (D.obj
          j).hom)) hw q
        (((pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u +
          1}]).obj (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
        (((pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u +
          1}]).obj (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
        ((upperStarComp AddCommGrpCat.{u + 1} (show pullback (D.map m.hom).left (pullback.snd f
          (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
          ((cartesianChartDiagram f D j).map a).left)
          (pullback.snd (D.map l.hom).left (pullback.snd f (D.obj j).hom))
          (pullback.snd (D.map m.hom).left (pullback.snd f (D.obj j).hom)) hl2.symm).inv.app
            (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W ((asIso
            (rawRestrictedCohomologyComparison (pullback.snd (D.map l.hom).left (pullback.snd f
            (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map l.hom).left
            (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
            j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv x) at hz0
    simpa only [hBl_hom, hBm_hom] using hz0
  exact hz''

end CartesianChartLiftNaturality
end AlgebraicGeometry.Etale
