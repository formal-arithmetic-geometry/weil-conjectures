/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.SecSmoothPurity.ChartFiniteRingAdjunction

/-! # Evaluation of the geometric chart counit on an etale representative

Source: blueprint sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-exceptional.proof.md`, Charts, comparison of the actual counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.ChartFiniteRing
open AdjunctionTransfer

set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.mapDerivedCategoryPlus Etale.rightDerivedLowerStarPlus

/-- The fixed proper-mate/open comparison agrees with the canonical compact-support
site comparison on bounded below inputs. Both use the same proper mate. The exact
open comparison restricts from the ambient derived category to `D+`, and naturality
of the proper direct-image inclusion comparison identifies the remaining factors.
Source: the compact-support comparison calculation in
`sk-lem-sp-reduction-exceptional.proof.md`, Charts. -/
private theorem fixedComparison_eq
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (fixedCompactSupportComparisonIso R c).hom.app K =
      (compactSupportSiteComparison R c).hom.app K := by
  let O := openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) c.i
  let o := properOpenSiteExtensionIso R c.i
  let q := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso O ≪≫ Functor.mapDerivedCategoryCompIso _ _
  have ho : _root_.DerivedCategory.Plus.ι.mapIso (o.app K) = q.app K.obj := by
    have h₁ : _root_.DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusCompIso
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)
          (comparisonUpperStar (ModuleCat.{u + 1} R) c.Z)).app K) =
        (Functor.mapDerivedCategoryCompIso
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)
          (comparisonUpperStar (ModuleCat.{u + 1} R) c.Z)).app K.obj := by
      apply Iso.ext
      exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ K
    have h₂ : _root_.DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusCompIso
          (comparisonUpperStar (ModuleCat.{u + 1} R) X)
          (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)).app K) =
        (Functor.mapDerivedCategoryCompIso
          (comparisonUpperStar (ModuleCat.{u + 1} R) X)
          (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i)).app K.obj := by
      apply Iso.ext
      exact Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app _ _ K
    have h₃ : _root_.DerivedCategory.Plus.ι.mapIso
        ((Functor.mapDerivedCategoryPlusNatIso O).app K) =
        (Functor.mapDerivedCategoryNatIso O).app K.obj := by
      apply Iso.ext
      exact Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app O K
    change _root_.DerivedCategory.Plus.ι.mapIso
      (((Functor.mapDerivedCategoryPlusCompIso _ _).app K).symm ≪≫
        (Functor.mapDerivedCategoryPlusNatIso O).app K ≪≫
        (Functor.mapDerivedCategoryPlusCompIso _ _).app K) = _
    rw [Functor.mapIso_trans, Functor.mapIso_trans, Functor.mapIso_symm, h₁, h₂, h₃]
    rfl
  have hoi := congrArg Iso.inv ho
  change _root_.DerivedCategory.Plus.ι.map (o.inv.app K) = q.inv.app K.obj at hoi
  have hn :=
    (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctorPlusCompatibility.inv.naturality
      (o.inv.app K)
  dsimp only [fixedCompactSupportComparisonIso, fixedDirectImageComparisonIso,
    compactSupportSiteComparison, compactSupportSiteComparisonPlus,
    rightDerivedLowerShriekOfCompactificationPlusCompatibility,
    Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.map_comp,
    Category.id_comp, Category.comp_id, Category.assoc]
  simp only [Functor.comp_map]
  repeat' erw [Category.id_comp]
  repeat' erw [Category.comp_id]
  simp only [Functor.comp_map, hoi] at hn
  dsimp only [q, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app] at hn
  simp only [Functor.map_comp, Category.assoc] at hn
  have hs : (Functor.mapDerivedCategoryNatIso O.symm).hom =
      (Functor.mapDerivedCategoryNatIso O).inv := rfl
  rw [hs]
  have := isIso_fixedComparisonDirectImageMatePlus R c.g
  let tail := _root_.DerivedCategory.Plus.ι.map
    ((asIso (fixedComparisonDirectImageMatePlus R c.g)).inv.app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategoryPlus.obj K)) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.map
      ((Etale.lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctorPlusCompatibility.hom.app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategoryPlus.obj K))
  erw [(comparisonUpperStar (ModuleCat.{u + 1} R) c.Z).mapDerivedCategory.map_id,
    (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctor.map_id,
    (Etale.lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctor.map_id,
    (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.map_id,
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.map_id,
    (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctor.map_id]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]
  erw [Category.comp_id]
  exact (reassoc_of% hn) tail

/-- Evaluation of the specified geometric counit on any etale representative,
including the endpoint isomorphism. This is a single-ring identity and requires
no coefficient comparison.

Source: blueprint sec-smooth-purity/sk-lem-sp-reduction,
`sk-lem-sp-reduction-exceptional.proof.md`, Charts, transported counit and
canonical tensor/pullback comparison
(blueprint: lem-sp-chart-geometric-counit-evaluation).

Proof: The ordered affine normalization is the component of towerENormalForm.
Whisker it with etale pullback, then compose with tensorEPullback and the
inverse-image composition isomorphism. This gives the natural ordinary chart
normalization. Compose its comparison inverse image with the signed shift
comparison, the comparison functor's tensor comparison, its comparison on
single sheaves, and the site/pullback interchange. Its components are exactly
chartGeometryComponent, so these components are natural in the input.
At eY(J), geometric_normalization and naturality at eY.unitIso.inv(J) identify
geometric.hom with eU(H(unitIso.inv(J))) followed by the geometric component
at J, using the equivalence triangle identity. Substitute proCounit(J) and
cancel the inverse geometric identification and the image of the unit.
The remaining composite is cf.inv(H(J)) followed by eY of the etale counit.
Apply fixedComparison: the direct-image factor is the fixed proper mate and
the open factor is the exact open site comparison. Expand
fixedCompactSupportComparisonIso and compactSupportSiteComparison into their
proper and open factors. The open comparison on bounded below complexes maps
to the ambient open comparison; naturality of rightDerivedFunctorPlusCompatibility
moves it across the proper inclusion comparison. The exact inclusion comparisons
are identities, leaving equal proper-counit mates and equal open factors.
Finally use naturality of the geometric counit at the given endpoint isomorphism
from the comparison image of J to K. This yields the displayed equality on every K.
-/
theorem chartGeometricCounitEvaluation
    (R : Type (u + 1)) [CommRing R] [Finite R]
    {U Y : Scheme.{u}} [IsNoetherian U] [IsNoetherian Y]
    (N : ℕ) (hR : (N : R) = 0) (d : ℕ) (e : U ⟶ affineTraceTower Y d)
    [AlgebraicGeometry.Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (cp : Compactification (affineTraceProjection Y d))
    (cg : Compactification (e ≫ affineTraceProjection Y d))
    (M : Etale.EtaleCompactSupportNormalization R)
    (t : Etale.OrdinaryFiniteTwistTransport R N hR)
    (P : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum R N hR t T hT)
    (hY : IsUnit (N : Γ(Y, ⊤))) (C : Datum R N hR d e cp cg M t P hY)
    (J : (etaleProperty R Y).FullSubcategory)
    (K : (proEtaleProperty R Y).FullSubcategory)
    (a : (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.obj J.obj ≅
      K.obj) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).map
        ((chartGeometryComponent R N C.positive hR C.flatTwist hY d e J.obj).hom ≫
          (geometricRight R N hR d e).map a.hom) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg).map
        (C.geometric.inv.app K).hom ≫ (C.adjPro.counit.app K).hom =
    (compactSupportSiteComparison R cg).hom.app
        ((etaleToPlus R U).obj ((etaleRight R N hR d e C.hRight).obj J)) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory.map
        (C.adjEt.counit.app J).hom ≫ a.hom := by
  rcases C with ⟨positive, flatTwist, intrinsic, hEt, hRight, hPro, hU, hV,
    eU, eY, heU, heY, adjEt, etaleCounit, cf, fixedComparison, adjPro, proCounit,
    hGeometry, geometric, geometric_normalization, brown⟩
  rcases eU with ⟨EU, IU, uU, cU, trU⟩
  rcases eY with ⟨EY, IY, uY, cY, trY⟩
  dsimp only at heU heY
  subst EU
  subst EY
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) cg
  let G := geometricRight R N hR d e
  let V := (comparisonUpperStar (ModuleCat.{u + 1} R) Y).mapDerivedCategory
  let W := (comparisonUpperStar (ModuleCat.{u + 1} R) U).mapDerivedCategory
  let H := etaleRight R N hR d e hRight
  let γ := chartGeometryIso R N positive hR flatTwist hY d e
  have hn := γ.hom.naturality (uY.inv.app J).hom
  have hg := geometric_normalization ((comparison R Y hV).obj J)
  have hp := congrArg (fun f ↦ f.hom) (proCounit J)
  simp only [eqToHom_refl, Category.id_comp, chartGeometryComponent] at hg
  have hc : (cY.hom.app ((comparison R Y hV).obj J)).hom =
      V.map (uY.inv.app J).hom := by
    exact congrArg (fun f ↦ f.hom)
      ((Equivalence.mk' (comparison R Y hV) IY uY cY trY).counit_app_functor J)
  rw [hc] at hg
  change W.map ((Etale.affineTraceRight R N hR Y d ⋙
    Etale.ordinaryFinitePullback R e).map (uY.inv.app J).hom) ≫
      (γ.hom.app J.obj) = _ at hn
  change (geometric.hom.app ((comparison R Y hV).obj J)).hom = _ at hg
  have hgeom : (geometric.hom.app ((comparison R Y hV).obj J)).hom =
      W.map (H.map (uY.inv.app J)).hom ≫ γ.hom.app J.obj := hg.trans hn.symm
  have hcancel : γ.hom.app J.obj ≫
      (geometric.inv.app ((comparison R Y hV).obj J)).hom ≫
        W.map (H.map (uY.inv.app J)).hom = 𝟙 _ := by
    apply (cancel_mono (γ.hom.app J.obj)).1
    simp only [Category.assoc, Category.id_comp]
    rw [← hgeom]
    have hi := congrArg (fun f ↦ f.hom)
      (geometric.inv_hom_id_app ((comparison R Y hV).obj J))
    change (geometric.inv.app ((comparison R Y hV).obj J)).hom ≫
      (geometric.hom.app ((comparison R Y hV).obj J)).hom = 𝟙 _ at hi
    change (geometric.inv.app ((comparison R Y hV).obj J)).hom ≫
      (geometric.hom.app ((comparison R Y hV).obj J)).hom =
        𝟙 (G.obj (V.obj J.obj)) at hi
    exact (congrArg (fun f ↦ γ.hom.app J.obj ≫ f) hi).trans (Category.comp_id _)
  have hbase : F.map (γ.hom.app J.obj) ≫
      F.map (geometric.inv.app ((comparison R Y hV).obj J)).hom ≫
        (adjPro.counit.app ((comparison R Y hV).obj J)).hom =
      (cf.inv.app (H.obj J)).hom ≫ V.map (adjEt.counit.app J).hom := by
    rw [hp]
    change F.map (γ.hom.app J.obj) ≫
      F.map (geometric.inv.app ((comparison R Y hV).obj J)).hom ≫
      (F.map (W.map (H.map (uY.inv.app J)).hom) ≫
        (cf.inv.app (H.obj J)).hom ≫ V.map (adjEt.counit.app J).hom) = _
    simp only [← F.map_comp_assoc, hcancel, F.map_id, Category.id_comp]
  have hcf := fixedComparison (H.obj J)
  simp only [eqToHom_refl, Category.comp_id] at hcf
  rw [hcf, fixedComparison_eq] at hbase
  let δ := Functor.whiskerRight geometric.inv (proEtaleLowerShriek R cg hPro) ≫
    adjPro.counit
  let a' : (comparison R Y hV).obj J ⟶ K := ObjectProperty.homMk a.hom
  have hnδ := congrArg (fun f ↦ f.hom) (δ.naturality a')
  change F.map (G.map a.hom) ≫
      (F.map (geometric.inv.app K).hom ≫ (adjPro.counit.app K).hom) =
    (F.map (geometric.inv.app ((comparison R Y hV).obj J)).hom ≫
      (adjPro.counit.app ((comparison R Y hV).obj J)).hom) ≫ a.hom at hnδ
  simp only [chartGeometryComponent]
  change F.map ((γ.hom.app J.obj) ≫ G.map a.hom) ≫
    F.map (geometric.inv.app K).hom ≫ (adjPro.counit.app K).hom =
      (compactSupportSiteComparison R cg).hom.app ((etaleToPlus R U).obj (H.obj J)) ≫
        V.map (adjEt.counit.app J).hom ≫ a.hom
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [hnδ, ← Category.assoc, hbase]
  rw [F.map_id]
  simp only [Category.assoc]
  change 𝟙 _ ≫ ((compactSupportSiteComparison R cg).hom.app
    ((etaleToPlus R U).obj (H.obj J)) ≫ V.map (adjEt.counit.app J).hom ≫ a.hom) = _
  exact Category.id_comp _

end AlgebraicGeometry.ProEtale.ChartFiniteRing
