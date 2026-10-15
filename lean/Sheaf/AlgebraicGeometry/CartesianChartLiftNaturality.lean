/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CartesianChartClassPullback
import Sheaf.AlgebraicGeometry.CartesianChartExchangeMapBridge
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeComparison
import all Sheaf.AlgebraicGeometry.AbelianRawPullbackComposition
import all Sheaf.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift

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
  rawAffineRestrictedCohomologyMap
  rawAffineComplexPullback cohomology
  rightDerivedGlobalSections DerivedCategory.Q
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

private theorem shift_pull_comp_pair {C D E : Type*}
    [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (α : H ≅ F ⋙ G) [NatTrans.CommShift α.hom ℤ]
    (M K : C) (N N₀ : D) (P P₀ P₁ : E) (q : ℤ)
    (sa₁ : N ⟶ N₀) (sa₂ : N₀ ⟶ F.obj M)
    (sb₁ : P ⟶ P₀) (sb₂ : P₀ ⟶ G.obj N)
    (sd₁ : P ⟶ P₁) (sd₂ : P₁ ⟶ H.obj M)
    (hs : (sb₁ ≫ sb₂) ≫ G.map (sa₁ ≫ sa₂) =
      (sd₁ ≫ sd₂) ≫ α.hom.app M) (z : M ⟶ K⟦q⟧) :
    sd₁ ≫ sd₂ ≫ H.map z ≫ (H.commShiftIso q).hom.app K ≫
      (shiftFunctor E q).map (α.hom.app K) =
    sb₁ ≫ sb₂ ≫ G.map (sa₁ ≫ sa₂ ≫ F.map z ≫
      (F.commShiftIso q).hom.app K) ≫ (G.commShiftIso q).hom.app (F.obj K) := by
  simpa only [Category.assoc] using
    shift_pull_comp F G H α M K N P q (sa₁ ≫ sa₂) (sb₁ ≫ sb₂)
      (sd₁ ≫ sd₂) hs z

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
    cartesianChartClassPullbackCore h d s hs M K q z ≫
      (shiftFunctor _ q).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} b a d hd).hom.app K) =
    cartesianChartClassPullbackCore h' b s (by rw [hs, hd, hh', Category.assoc]) M
      ((D+((a)^*[AddCommGrpCat.{u + 1}])).obj K) q
      (cartesianChartClassPullbackCore h a h' hh' M K q z) := by
  subst d
  subst h'
  rw [Category.assoc] at hs
  cases hs
  unfold cartesianChartClassPullbackCore
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
  exact shift_pull_comp_pair
    (D+((a)^*[AddCommGrpCat.{u + 1}])) (D+((b)^*[AddCommGrpCat.{u + 1}]))
    (D+((b ≫ a)^*[AddCommGrpCat.{u + 1}]))
    (upperStarPlusComp AddCommGrpCat.{u + 1} b a)
    ((DerivedCategory.Plus.singleFunctor _ 0).obj (((h)^*[AddCommGrpCat.{u + 1}]).obj M))
    K _ _ _ _ _ q
    ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} a h).hom.app M))
    ((((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _)
    ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} b (a ≫ h)).hom.app M))
    ((((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _)
    ((DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} (b ≫ a) h (b ≫ a ≫ h)
        (Category.assoc b a h).symm).hom.app M))
    ((((b ≫ a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _)
    (by simpa only [Category.assoc] using hs) z

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
      (cartesianChartClassPullbackCore h a h' hh' ((abelianComparisonFree B).obj W) K q z) := by
  have e := chart_pull_comp_core h a b d hd h' hh' s hs
    ((abelianComparisonFree B).obj W) K q z
  let p := (DerivedCategory.Plus.singleFunctor _ 0).map
    (abelianFreeRepresentablePullbackSquareIso s W V r hr).hom
  change (p ≫ _) ≫ _ = p ≫ _
  rw [Category.assoc]
  exact congrArg (fun t ↦ p ≫ t) e

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
  simp only [cartesianChartClassPullback, cartesianChartClassPullbackCore,
    Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]



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
  simpa only [cartesianChartClassPullbackCore, Category.assoc] using
    chartRawAdj_pullback f g a g' w b a' ha g'' w' wb l hl₁ hl₂ hw F n W z z' hz'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
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
  let k := pullback.snd f (D.obj j).hom
  let t : pullback (D.map m.hom).left k ⟶ pullback (D.map l.hom).left k :=
    ((cartesianChartDiagram f D j).map a).left
  have ht₁ : t ≫ pullback.fst (D.map l.hom).left k =
      pullback.fst (D.map m.hom).left k ≫ (D.map a.left).left := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _
  have ht₂ : t ≫ pullback.snd (D.map l.hom).left k =
      pullback.snd (D.map m.hom).left k := by
    exact Over.w ((cartesianChartDiagram f D j).map a)
  let h := pullback.snd (D.map l.hom).left k ≫ k
  let h' := pullback.snd (D.map m.hom).left k ≫ k
  have ht : t ≫ h = h' :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun v ↦ v ≫ k) ht₂)
  let G := ((pullback.snd (D.map l.hom).left k)^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let G' := ((pullback.snd (D.map m.hom).left k)^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let φ : ((t)^*[AddCommGrpCat.{u + 1}]).obj G ⟶ G' :=
    (upperStarComp AddCommGrpCat.{u + 1} t
    (pullback.snd (D.map l.hom).left k) (pullback.snd (D.map m.hom).left k)
    ht₂.symm).inv.app (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let x₀ : rawAffineRestrictedCohomology h q G W := x
  let z := rawRestrictedCohomologyClass h q G W x₀
  let y : rawAffineRestrictedCohomology h' q G' W := restrictedOverCohomologyMap k
    (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
    (q : ℤ) ((cartesianChartDiagram f D j).map a) W x
  let z' := rawRestrictedCohomologyClass h' q G' W y
  have hy : y = rawAffineRestrictedCohomologyMap t h h' ht q G G' φ W x₀ := by
    exact congrArg (fun v ↦ v x)
      (restrictedOverCohomologyMap_eq_rawAffine k
        (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
        q ((cartesianChartDiagram f D j).map a) W ht)
  have hz' : z' = abelianHigherDirectImageRawPullback t h h' ht q G G' φ W z := by
    exact (congrArg (rawRestrictedCohomologyClass h' q G' W) hy).trans
      (rawRestrictedCohomologyClass_naturality t h h' ht q G G' φ W x₀)
  with_unfolding_all exact (chartPull_adj_naturality f (D.obj j).hom (D.map l.hom).left
    (D.obj l.left).hom (Over.w (D.map l.hom)).symm (D.map a.left).left
    (D.map m.hom).left
    (by simpa only [D.map_comp, Over.comp_left] using
      congrArg (fun v ↦ (D.map v).left) (Over.w a).symm)
    (D.obj m.left).hom (Over.w (D.map m.hom)).symm
    (Over.w (D.map a.left)).symm t ht₁ ht₂ ht
    (c.π.app l.left).left (c.π.app m.left).left
    (congrArg (fun v ↦ v.left) (c.w a.left)).symm
    (c.π.app j).left (congrArg (fun v ↦ v.left) (c.w l.hom)).symm
    F q W V r hr z z' hz')

end AlgebraicGeometry.Etale
