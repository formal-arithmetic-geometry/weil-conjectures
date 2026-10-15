/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CartesianChartClassPullback
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison
import all Sheaf.AlgebraicGeometry.AbelianRawPullbackComposition
import all Sheaf.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift
import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-! # Chart lifts commute with stage transitions

Source: Stacks Project, Tags 0EYM, 03CB and 03Q8.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] restrictedOverCohomologyMap
  cartesianDerivedImageMap cartesianChartCohomologyLift upperStar upperStarCompDerivedPlus
  cartesianChartRawAdjunctionIso rawRestrictedCohomologyComparison
set_option backward.isDefEq.respectTransparency true

private theorem shift_pull_comp {C D E : Type*}
    [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (α : H ≅ F ⋙ G) [NatTrans.CommShift α.hom ℤ]
    (M K : C) (N : D) (P : E) (q : ℤ)
    (sa : N ⟶ F.obj M) (sb : P ⟶ G.obj N) (sd : P ⟶ H.obj M)
    (hs : sb ≫ G.map sa = sd ≫ α.hom.app M) (z : M ⟶ K⟦q⟧) :
    sd ≫ H.map z ≫ (H.commShiftIso q).hom.app K ≫
      (shiftFunctor E q).map (α.hom.app K) =
    sb ≫ G.map (sa ≫ F.map z ≫ (F.commShiftIso q).hom.app K) ≫
      (G.commShiftIso q).hom.app (F.obj K) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs]
  rw [← reassoc_of% (α.hom.naturality z)]
  rw [← Functor.commShiftIso_comp_hom_app]
  rw [NatTrans.shift_app_comm]

private theorem chart_pull_comp_core {B T T' T'' : Scheme.{u}}
    (h : T ⟶ B) (a : T' ⟶ T) (b : T'' ⟶ T')
    (d : T'' ⟶ T) (hd : d = b ≫ a)
    (h' : T' ⟶ B) (hh' : h' = a ≫ h)
    (s : T'' ⟶ B) (hs : s = d ≫ h)
    (M : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{u + 1}]).obj M) ⟶ K⟦q⟧) :
    ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} d h s hs).hom.app M) ≫
      (((d)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
      (D+((d)^*[AddCommGrpCat.{u + 1}])).map z ≫
      (D+((d)^*[AddCommGrpCat.{u + 1}]).commShiftIso q).hom.app K) ≫
      (shiftFunctor _ q).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a d hd).hom.app K) =
    (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} b h' s
          (by rw [hs, hd, hh', Category.assoc])).hom.app M) ≫
      (((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
      (D+((b)^*[AddCommGrpCat.{u + 1}])).map
      ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} a h h' hh').hom.app
            M) ≫
        (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
        (D+((a)^*[AddCommGrpCat.{u + 1}])).map z ≫
        (D+((a)^*[AddCommGrpCat.{u + 1}]).commShiftIso q).hom.app K) ≫
      (D+((b)^*[AddCommGrpCat.{u + 1}]).commShiftIso q).hom.app
        ((D+((a)^*[AddCommGrpCat.{u + 1}])).obj K) := by
  subst d
  subst h'
  rw [Category.assoc] at hs
  cases hs
  rw [upperStarCompDerivedPlus_eq_eqToIso_trans]
  simp only [eqToIso_refl, Iso.refl_trans]
  simp only [Category.assoc]
  have hs := sourceComp AddCommGrpCat.{u + 1} h a b M
  have : NatTrans.CommShift
      (upperStarPlusComp AddCommGrpCat.{u + 1} b a).hom ℤ := by
    have := Functor.plusNatIso_commShift (upperStarComp AddCommGrpCat.{u + 1} b a)
    have := Functor.plusCompIso_commShift (a)^*[AddCommGrpCat.{u + 1}]
      (b)^*[AddCommGrpCat.{u + 1}]
    unfold upperStarPlusComp
    dsimp only [Iso.trans_hom]
    infer_instance
  let sa := (DerivedCategory.Plus.singleFunctor _ 0).map
    ((upperStarComp AddCommGrpCat.{u + 1} a h).hom.app M) ≫
      (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _
  let sb := (DerivedCategory.Plus.singleFunctor _ 0).map
    ((upperStarComp AddCommGrpCat.{u + 1} b (a ≫ h)).hom.app M) ≫
      (((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _
  let sd := (DerivedCategory.Plus.singleFunctor _ 0).map
    ((upperStarComp AddCommGrpCat.{u + 1} (b ≫ a) h (b ≫ a ≫ h)
      (Category.assoc b a h).symm).hom.app M) ≫
      (((b ≫ a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _
  have e := shift_pull_comp
    (D+((a)^*[AddCommGrpCat.{u + 1}])) (D+((b)^*[AddCommGrpCat.{u + 1}]))
    (D+((b ≫ a)^*[AddCommGrpCat.{u + 1}]))
    (upperStarPlusComp AddCommGrpCat.{u + 1} b a)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (((h)^*[AddCommGrpCat.{u + 1}]).obj M))
    K _ _ q sa sb sd
      (by simpa only [sa, sb, sd, Category.assoc] using hs) z
  dsimp only [sa, sb, sd] at e
  simpa only [Functor.map_comp, Category.assoc] using e
private theorem chart_pull_comp {B T T' T'' : Scheme.{u}}
    (h : T ⟶ B) (a : T' ⟶ T) (b : T'' ⟶ T')
    (d : T'' ⟶ T) (hd : d = b ≫ a)
    (h' : T' ⟶ B) (hh' : h' = a ≫ h)
    (s : T'' ⟶ B) (hs : s = d ≫ h)
    (W : B.Etale) (V : T''.Etale) (r : V.left ⟶ W.left)
    (hr : IsPullback r V.hom W.hom s)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj W)) ⟶ K⟦q⟧) :
    cartesianChartClassPullback h d s hs W V r hr K q z ≫
      (shiftFunctor _ q).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a d hd).hom.app K) =
    cartesianChartClassPullback h' b s (by rw [hs, hd, hh', Category.assoc]) W V r hr
      ((D+((a)^*[AddCommGrpCat.{u + 1}])).obj K) q
      ((DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} a h h' hh').hom.app
            ((abelianComparisonFree B).obj W)) ≫
        (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
        (D+((a)^*[AddCommGrpCat.{u + 1}])).map z ≫
        (D+((a)^*[AddCommGrpCat.{u + 1}]).commShiftIso q).hom.app K) := by
  have e := chart_pull_comp_core h a b d hd h' hh' s hs
    ((abelianComparisonFree B).obj W) K q z
  simpa only [cartesianChartClassPullback, Category.assoc] using congrArg
    (fun t ↦ (DerivedCategory.Plus.singleFunctor _ 0).map
      (abelianFreeRepresentablePullbackSquareIso s W V r hr).hom ≫ t) e

private theorem chartClassPullback_postcomp {B T T' : Scheme.{u}}
    (a : T ⟶ B) (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (W : B.Etale) (V : T'.Etale) (r : V.left ⟶ W.left)
    (hr : IsPullback r V.hom W.hom a')
    (K L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ)
    (y : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj W)) ⟶ K⟦q⟧)
    (e : K ⟶ L) :
    cartesianChartClassPullback a b a' ha W V r hr K q y ≫
        (shiftFunctor _ q).map ((D+((b)^*[AddCommGrpCat.{u + 1}])).map e) =
      cartesianChartClassPullback a b a' ha W V r hr L q
        (y ≫ (shiftFunctor _ q).map e) := by
  simp only [cartesianChartClassPullback, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]



private theorem rawComparison_inv_naturality {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (q : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ((a)^*[AddCommGrpCat.{u + 1}]).obj F ⟶ F') (W : S.Etale)
    [IsIso (rawRestrictedCohomologyComparison h q F W)]
    [IsIso (rawRestrictedCohomologyComparison h' q F' W)]
    (x : rawAffineRestrictedCohomology h q F W) :
    (asIso (rawRestrictedCohomologyComparison h' q F' W)).inv
      (rawAffineRestrictedCohomologyMap a h h' w q F F' φ W x) =
    abelianHigherDirectImageRawPullback a h h' w q F F' φ W
      ((asIso (rawRestrictedCohomologyComparison h q F W)).inv x) := by
  let R := asIso (rawRestrictedCohomologyComparison h q F W)
  let R' := asIso (rawRestrictedCohomologyComparison h' q F' W)
  have hraw := rawRestrictedCohomologyComparison_naturality a h h' w q F F' φ W
    (R.inv x)
  change rawAffineRestrictedCohomologyMap a h h' w q F F' φ W (R.hom (R.inv x)) =
    R'.hom (abelianHigherDirectImageRawPullback a h h' w q F F' φ W (R.inv x)) at hraw
  rw [Iso.inv_hom_id_apply] at hraw
  exact (congrArg (fun y ↦ R'.inv y) hraw).trans (Iso.hom_inv_id_apply R' _)

private theorem chartPull_adj_naturality {S X B T T' : Scheme.{u}}
    (f : X ⟶ S) (g : B ⟶ S) (a : T ⟶ B) (g' : T ⟶ S) (w : g' = a ≫ g)
    (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (g'' : T' ⟶ S) (w' : g'' = a' ≫ g) (wb : g'' = b ≫ g')
    (l : pullback a' (pullback.snd f g) ⟶ pullback a (pullback.snd f g))
    (hl₁ : l ≫ pullback.fst a (pullback.snd f g) =
      pullback.fst a' (pullback.snd f g) ≫ b)
    (hl₂ : l ≫ pullback.snd a (pullback.snd f g) = pullback.snd a' (pullback.snd f g))
    (hw : l ≫ (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) =
      pullback.snd a' (pullback.snd f g) ≫ pullback.snd f g)
    {A : Scheme.{u}} (σ : A ⟶ T) (τ : A ⟶ T') (hσ : σ = τ ≫ b)
    (ρ : A ⟶ B) (hρ : ρ = σ ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (W : B.Etale) (V : A.Etale) (r : V.left ⟶ W.left)
    (hr : IsPullback r V.hom W.hom ρ)
    (z : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op W))
    (z' : (abelianHigherDirectImageRawPresheaf
      (pullback.snd a' (pullback.snd f g) ≫ pullback.snd f g) n
      (((pullback.snd a' (pullback.snd f g))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op W))
    (hz' : z' = abelianHigherDirectImageRawPullback l
      (pullback.snd a (pullback.snd f g) ≫ pullback.snd f g)
      (pullback.snd a' (pullback.snd f g) ≫ pullback.snd f g) hw n _ _
      ((upperStarComp AddCommGrpCat.{u + 1} l
        (pullback.snd a (pullback.snd f g)) (pullback.snd a' (pullback.snd f g))
        hl₂.symm).inv.app (((pullback.fst f g)^*[AddCommGrpCat.{u + 1}]).obj F)) W z) :
    cartesianChartClassPullback a σ ρ hρ W V r hr _ (n : ℤ)
      ((cartesianChartRawAdjunctionIso f g a g' w F n W).hom z) ≫
      (shiftFunctor _ (n : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} τ b σ hσ).hom.app _ ≫
          (D+((τ)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f g' g'' b wb
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) =
      cartesianChartClassPullback a' τ ρ (by rw [hρ, hσ, ha, Category.assoc])
        W V r hr _ (n : ℤ)
        ((cartesianChartRawAdjunctionIso f g a' g'' w' F n W).hom z') := by
  rw [Functor.map_comp, ← Category.assoc]
  rw [chart_pull_comp a b τ σ hσ a' ha ρ hρ W V r hr]
  rw [chartClassPullback_postcomp]
  congr 1
  simpa only [Category.assoc] using
    chartRawAdj_pullback f g a g' w b a' ha g'' w' wb l hl₁ hl₂ hw F n W z z' hz'

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
  sorry

end AlgebraicGeometry.Etale
