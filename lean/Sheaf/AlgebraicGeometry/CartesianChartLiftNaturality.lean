/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeComparison
import all WeilConjectures.AlgebraicGeometry.AbelianRawPullbackComposition
import all WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift
import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality
import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeMapNaturality
import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeConclusion
import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeFinal
import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeObjects
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

public import Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence
import Sheaf.AlgebraicGeometry.CartesianChartDiagramMap
import Sheaf.AlgebraicGeometry.CartesianChartLiftRawNaturality

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
/-- A chart lift intertwines the restricted cohomology map with cartesian exchange.

Source: Stacks Project, Tag 0EYM, the canonical comparison square; Tags 03CB and 03Q8.
(blueprint: lem-sc-cartesian-chart-lift-naturality).

Proof: Apply raw restricted evaluation naturality to the chart arrow and the inverse
composition comparison on its coefficients. Invert the evaluation comparison and
transport the resulting equality through the chart source isomorphisms. Pullback
uniqueness identifies the transported chart arrow with the cartesian projection.
The coefficient compositions agree by upperStarComp associativity. Under the derived
adjunction for the projection to the stage base, the exchanged class is the pullback
of the original adjunct: expand exchange as its adjunction mate and cancel the unit
and counit. The exact inverse-image single and shift comparisons commute with this
calculation. Pull back to the cone point, using the cone equation to identify the
free-sheaf sources. This proves the equality of the specified maps. No limit,
cofilteredness, affineness, qcqs hypothesis, or invertibility of exchange is used.
-/
theorem cartesianChartCohomologyLift_naturality
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (j : I) (W : (D.obj j).left.Etale) (V : c.pt.left.Etale)
    (r : V.left ⟶ W.left)
    (hr : IsPullback r V.hom W.hom (c.π.app j).left)
    (l m : Over j) (a : m ⟶ l)
    (x : restrictedOverCohomology (pullback.snd f (D.obj j).hom)
      (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D j).obj l) W) :
    cartesianChartCohomologyLift f D c F q j W V r hr l x ≫
      (shiftFunctor _ (q : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
          (c.π.app m.left).left (D.map a.left).left (c.π.app l.left).left
          (congrArg (fun t ↦ t.left) (c.w a.left)).symm).hom.app _ ≫
          (D+(((c.π.app m.left).left)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f (D.obj l.left).hom (D.obj m.left).hom
              (D.map a.left).left (Over.w (D.map a.left)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) =
      cartesianChartCohomologyLift f D c F q j W V r hr m
        (restrictedOverCohomologyMap (pullback.snd f (D.obj j).hom)
          (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
          (q : ℤ) ((cartesianChartDiagram f D j).map a) W x) := by
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
          j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv x) :=
    chart_inverse_comparison_map f D c F q j W V r hr l m a x hl2 hw
  have hcomp := chartPull_adj_naturality
    f (D.obj j).hom (D.map l.hom).left (D.obj l.left).hom
      (Over.w (D.map l.hom)).symm (D.map a.left).left
      (D.map m.hom).left (by
        calc
          (D.map m.hom).left = (D.map (a.left ≫ l.hom)).left := by
            exact congrArg (fun t ↦ (D.map t).left) (Over.w a).symm
          _ = (D.map a.left ≫ D.map l.hom).left := by
            rw [D.map_comp])
      (D.obj m.left).hom (Over.w (D.map m.hom)).symm (by
        exact (Over.w (D.map a.left)).symm) (show pullback (D.map m.hom).left (pullback.snd f
          (D.obj j).hom) ⟶ pullback (D.map l.hom).left (pullback.snd f (D.obj j).hom) from
          ((cartesianChartDiagram f D j).map a).left) hl1 hl2 hw
      (c.π.app l.left).left (c.π.app m.left).left
        (congrArg (fun t ↦ t.left) (c.w a.left)).symm
      (c.π.app j).left
        (congrArg (fun t ↦ t.left) (c.w l.hom)).symm F q W V r hr ((asIso
          (rawRestrictedCohomologyComparison (pullback.snd (D.map l.hom).left (pullback.snd f
          (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map l.hom).left
          (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
          j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv x) ((asIso
          (rawRestrictedCohomologyComparison (pullback.snd (D.map m.hom).left (pullback.snd f
          (D.obj j).hom) ≫ (pullback.snd f (D.obj j).hom)) q (((pullback.snd (D.map m.hom).left
          (pullback.snd f (D.obj j).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj
          j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) W)).inv (restrictedOverCohomologyMap
          (pullback.snd f (D.obj j).hom) (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u +
          1}]).obj F) (q : ℤ) ((cartesianChartDiagram f D j).map a) W x))
      hz''
  unfold cartesianChartCohomologyLift
  dsimp only 
  exact hcomp

end AlgebraicGeometry.Etale
