/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import Sheaf.AlgebraicGeometry.CompactificationProjectionComposition

/-! # Tensor projection maps and compact-support composition

Source: Stacks Project, `more-etale.tex`, Tags 0F7B and 0F7J, and
`sites-cohomology.tex`, Tag 0E48 (blueprint: lem-amb-shriek-tensor-composition).

The projection map is the existing proper/open compactification construction with both
factors exchanged by the canonical signed derived tensor symmetry. Exact termwise inverse
image is identified with left derived inverse image by its canonical comparison.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private theorem inverse_congr
    {C : Type*} [Category C] {X Y : C} {f g : X ⟶ Y} [IsIso f] [IsIso g]
    (h : f = g) : inv f = inv g := by
  subst g
  rfl

private theorem inverse_square
    {C : Type*} [Category C] {W X Y Z : C}
    (a : W ≅ X) (b : Y ≅ Z) (p : W ⟶ Y) (q : X ⟶ Z)
    (h : p ≫ b.hom = a.hom ≫ q) : q ≫ b.inv = a.inv ≫ p := by
  apply (cancel_mono b.hom).1
  simp only [Category.assoc, b.inv_hom_id, Category.comp_id, h, a.inv_hom_id_assoc]

private theorem projection_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F F' : C ⥤ D} {G : D ⥤ E} {H H' : C ⥤ E}
    (TD : D ⥤ D) (TE : E ⥤ E) (M N N' : C)
    (a : F' ≅ F) (b : H' ≅ H) (e : F' ⋙ G ≅ H')
    (pf : TD.obj (F.obj M) ⟶ F.obj N) (pf' : TD.obj (F'.obj M) ⟶ F'.obj N)
    (ph : TE.obj (H.obj M) ⟶ H.obj N') (ph' : TE.obj (H'.obj M) ⟶ H'.obj N')
    (q : N' ⟶ N) (pg : G ⋙ TE ⟶ TD ⋙ G)
    (hf : TD.map (a.hom.app M) ≫ pf = pf' ≫ a.hom.app N)
    (hh : ph' ≫ b.hom.app N' = TE.map (b.hom.app M) ≫ ph)
    (ht : pg.app (F'.obj M) ≫ G.map pf' ≫ e.hom.app N =
      TE.map (e.hom.app M) ≫ ph' ≫ H'.map q) :
    pg.app (F.obj M) ≫ G.map pf ≫
        (G.map (a.inv.app N) ≫ e.hom.app N ≫ b.hom.app N) =
      TE.map (G.map (a.inv.app M) ≫ e.hom.app M ≫ b.hom.app M) ≫ ph ≫ H.map q := by
  have hfi := inverse_square (TD.mapIso (a.app M)) (a.app N) pf' pf hf.symm
  have hfg := congrArg G.map hfi
  simp only [Functor.map_comp, Functor.mapIso_inv, Iso.app_inv] at hfg
  have hn := pg.naturality (a.inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Category.assoc, Functor.map_comp]
  rw [reassoc_of% hfg, ← reassoc_of% hn, reassoc_of% ht]
  rw [b.hom.naturality q, reassoc_of% hh]

private theorem tensor_projection_conjugation
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (V : E ⥤ E ⥤ E)
    (s : T ≅ T.flip) (t : U ≅ U.flip) (v : V ≅ V.flip)
    (Lf Df : D ⥤ C) (Lg Dg : E ⥤ D) (Lh Dh : E ⥤ C)
    (lf : Lf ≅ Df) (lg : Lg ≅ Dg) (lh : Lh ≅ Dh)
    (lc : Lh ≅ Lg ⋙ Lf) (dc : Dh ≅ Dg ⋙ Df) (a : F ⋙ G ≅ H)
    (M : C) (K : E)
    (pf : (U.obj (F.obj M)).obj (Lg.obj K) ⟶ F.obj ((T.obj M).obj (Lf.obj (Lg.obj K))))
    (pf' : (U.obj (F.obj M)).obj (Dg.obj K) ⟶ F.obj ((T.obj M).obj (Lf.obj (Dg.obj K))))
    (pg : (V.obj (G.obj (F.obj M))).obj K ⟶ G.obj ((U.obj (F.obj M)).obj (Lg.obj K)))
    (ph : (V.obj (H.obj M)).obj K ⟶ H.obj ((T.obj M).obj (Lh.obj K)))
    (hf : (U.obj (F.obj M)).map (lg.hom.app K) ≫ pf' =
      pf ≫ F.map ((T.obj M).map (Lf.map (lg.hom.app K))))
    (hc : lc.hom.app K ≫ Lf.map (lg.hom.app K) ≫ lf.hom.app (Dg.obj K) =
      lh.hom.app K ≫ dc.hom.app K)
    (ht : pg ≫ G.map pf ≫ a.hom.app ((T.obj M).obj (Lf.obj (Lg.obj K))) =
      (V.map (a.hom.app M)).app K ≫ ph ≫ H.map ((T.obj M).map (lc.hom.app K))) :
    (v.hom.app K).app (G.obj (F.obj M)) ≫ pg ≫
        G.map ((U.obj (F.obj M)).map (lg.hom.app K)) ≫
        G.map ((t.inv.app (Dg.obj K)).app (F.obj M)) ≫
        G.map ((t.hom.app (Dg.obj K)).app (F.obj M) ≫ pf' ≫
          F.map ((T.obj M).map (lf.hom.app (Dg.obj K))) ≫
          F.map ((s.inv.app (Df.obj (Dg.obj K))).app M)) ≫
        a.hom.app ((T.obj (Df.obj (Dg.obj K))).obj M) =
      (V.obj K).map (a.hom.app M) ≫ (v.hom.app K).app (H.obj M) ≫ ph ≫
        H.map ((T.obj M).map (lh.hom.app K)) ≫
        H.map ((s.inv.app (Dh.obj K)).app M) ≫ H.map ((T.map (dc.hom.app K)).app M) := by
  let r := (T.obj M).map (Lf.map (lg.hom.app K) ≫ lf.hom.app (Dg.obj K)) ≫
    (s.inv.app (Df.obj (Dg.obj K))).app M
  let q := (T.obj M).map (lh.hom.app K) ≫ (s.inv.app (Dh.obj K)).app M
  have hcr : (T.obj M).map (lc.hom.app K) ≫ r =
      q ≫ (T.map (dc.hom.app K)).app M := by
    dsimp only [r, q]
    rw [← Category.assoc, ← Functor.map_comp, hc, Functor.map_comp, Category.assoc]
    have hs : (T.obj M).map (dc.hom.app K) ≫
        (s.inv.app (Df.obj (Dg.obj K))).app M =
      (s.inv.app (Dh.obj K)).app M ≫ (T.map (dc.hom.app K)).app M :=
      congr_app (s.inv.naturality (dc.hom.app K)) M
    simpa only [Category.assoc] using
      congrArg (((T.obj M).map (lh.hom.app K)) ≫ ·) hs
  have ha := a.hom.naturality r
  dsimp only [Functor.comp_map] at ha
  have hv := (v.hom.app K).naturality (a.hom.app M)
  have hcancel : G.map ((t.inv.app (Dg.obj K)).app (F.obj M)) ≫
      G.map ((t.hom.app (Dg.obj K)).app (F.obj M) ≫ pf' ≫
        F.map ((T.obj M).map (lf.hom.app (Dg.obj K))) ≫
        F.map ((s.inv.app (Df.obj (Dg.obj K))).app M)) =
      G.map (pf' ≫ F.map ((T.obj M).map (lf.hom.app (Dg.obj K))) ≫
        F.map ((s.inv.app (Df.obj (Dg.obj K))).app M)) := by
    rw [← G.map_comp, Iso.inv_hom_id_app_app_assoc]
  rw [reassoc_of% hcancel]
  have hfg := congrArg G.map hf
  simp only [Functor.map_comp] at hfg
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hfg]
  have hr : G.map (F.map ((T.obj M).map (Lf.map (lg.hom.app K)))) ≫
      G.map (F.map ((T.obj M).map (lf.hom.app (Dg.obj K)))) ≫
      G.map (F.map ((s.inv.app (Df.obj (Dg.obj K))).app M)) = G.map (F.map r) := by
    simp only [r, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hr, ha]
  rw [reassoc_of% ht]
  have hh := congrArg H.map hcr
  simp only [Functor.map_comp] at hh
  rw [hh, reassoc_of% hv]
  simp only [q, Functor.map_comp, Category.assoc]
  rfl

namespace AlgebraicGeometry.Etale


/-- The coefficient-first compact-support tensor projection map on a specified compactification.
Source: Stacks Project, Tags 0B56, 0GL1, and 0F7I
(blueprint: lem-amb-shriek-tensor-composition).

The middle map is exactly the proper projection followed by the derived termwise
open-extension tensor comparison. The two symmetries and the exact-pullback comparison
only put its endpoints in the coefficient-first convention of this node.
-/
noncomputable def compactSupportProjectionMapOfCompactification
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj M) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).app M)

/-- The same canonical map on the chosen, compactification-independent compact-support functor.
Source: Stacks Project, Tags 0F7I and 0F7J
(blueprint: lem-amb-shriek-tensor-composition). -/
noncomputable def compactSupportProjectionMap
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).obj
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj M) :=
  compactSupportProjectionMapOfCompactification A
    (HasCompactification.compactification f) M K

private theorem compactSupportProjectionMap_eq
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    compactSupportProjectionMap A f M K =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app K).app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫
        ((projectionMap (ModuleCat.{u + 1} A) f).app M).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app
            ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).app M) := by
  dsimp only [compactSupportProjectionMap, compactSupportProjectionMapOfCompactification,
    projectionMap, rightDerivedLowerShriek]

section ProjectionProof
local instance essentiallySmall_etale_shriekTensorMain (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _
set_option backward.defeqAttrib.useBackward true
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize

set_option backward.isDefEq.respectTransparency false

-- Keep the large compactification and localization constructions behind their APIs.
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

attribute [local implicit_reducible] Compactification.restrict Compactification.ofIsPullback
  Compactification.comp Compactification.copy Compactification.postcomp

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor unboundedEtaleLowerShriekCompIso
  rightDerivedLowerShriekOfCompactificationIso
  rightDerivedLowerShriekOfCompactificationCompIso
  projectionMapOfCompactification derivedTensorSymmetry derivedTensor

-- The kernel checks the three specified compactification compositors.
private theorem projectionMap_compactification_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f) (d : Compactification g)
    (h : Compactification (f ≫ g)) (e : Compactification (f ≫ d.i))
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
    let G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d
    let H := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) h
    let T := derivedTensor (ModuleCat.{u + 1} A) X
    let U := derivedTensor (ModuleCat.{u + 1} A) Z
    let Lf := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    let Lg := (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    let E := Functor.isoWhiskerRight
      (rightDerivedLowerShriekOfCompactificationIso A e.restrict c).symm G ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A d e ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (d.comp e) h
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) d).app (F.obj M)).app K ≫
        G.map (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app (Lg.obj K)) ≫
        E.hom.app ((T.obj M).obj (Lf.obj (Lg.obj K))) =
      (U.map (E.hom.app M)).app K ≫
        ((projectionMapOfCompactification (ModuleCat.{u + 1} A) h).app M).app K ≫
        H.map ((T.obj M).map ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K)) := by
  have ht := projection_transport (F := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u +
    1} A) c)) (F' := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e.restrict))
    (G := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)) (H :=
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) h)) (H' :=
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) (d.comp e)))
    ((derivedTensor (ModuleCat.{u + 1} A) Y).flip.obj (((upperStar (ModuleCat.{u + 1} A)
      g).leftDerivedFunctor).obj K)) ((derivedTensor (ModuleCat.{u + 1} A) Z).flip.obj K) M
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj (((upperStar (ModuleCat.{u + 1} A)
      f).leftDerivedFunctor).obj (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K)))
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj (((upperStar (ModuleCat.{u + 1} A) (f ≫
      g)).leftDerivedFunctor).obj K))
    (rightDerivedLowerShriekOfCompactificationIso A e.restrict c)
      (rightDerivedLowerShriekOfCompactificationIso A (d.comp e) h)
      (rightDerivedLowerShriekOfCompactificationCompIso A d e) (((projectionMapOfCompactification
      (ModuleCat.{u + 1} A) c).app M).app (((upperStar (ModuleCat.{u + 1} A)
      g).leftDerivedFunctor).obj K)) (((projectionMapOfCompactification (ModuleCat.{u + 1} A)
      e.restrict).app M).app
    (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K))
      (((projectionMapOfCompactification (ModuleCat.{u + 1} A) h).app M).app K)
      (((projectionMapOfCompactification (ModuleCat.{u + 1} A) (d.comp e)).app M).app K)
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K)) (((flipFunctor _ _ _).map
    (projectionMapOfCompactification (ModuleCat.{u + 1} A) d)).app K)
    (projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
      A e.restrict c M (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K)).symm
    (projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
      A (d.comp e) h M K)
    (projectionMapOfCompactification_tower_comp A f g d e M K)
  simpa only [flipFunctor, Functor.flip, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Category.assoc] using ht

private theorem pullback_comparison_comp
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : DerivedCategoryModule A Z) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K ≫
        (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).hom.app K) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K) =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (f ≫ g)).hom.app K ≫
        (unboundedEtaleUpperStarCompIso A f g).hom.app K := by
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    unboundedEtaleUpperStarCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← (upperStar (ModuleCat.{u + 1} A)
    f).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [Category.comp_id]

end ProjectionProof

section TensorConventionProof
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint
  ModuleCat.hasColimitsOfShape ModuleCat.hasColimitsOfSize
local instance essentiallySmall_etale_tensorConvention (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor derivedTensorSymmetry derivedTensor
  unboundedEtaleLowerShriekCompIso projectionMapOfCompactification
attribute [local implicit_reducible] derivedTensorRightDerivedLowerShriek
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar

private theorem projectionMap_chosen_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    let F := rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
    let G := rightDerivedLowerShriek (ModuleCat.{u + 1} A) g
    let H := rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)
    let T := derivedTensor (ModuleCat.{u + 1} A) X
    let U := derivedTensor (ModuleCat.{u + 1} A) Z
    let Lf := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
    let Lg := (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor
    let E := unboundedEtaleLowerShriekCompIso A f g
    ((projectionMap (ModuleCat.{u + 1} A) g).app (F.obj M)).app K ≫
        G.map (((projectionMap (ModuleCat.{u + 1} A) f).app M).app (Lg.obj K)) ≫
        E.hom.app ((T.obj M).obj (Lf.obj (Lg.obj K))) =
      (U.map (E.hom.app M)).app K ≫
        ((projectionMap (ModuleCat.{u + 1} A) (f ≫ g)).app M).app K ≫
        H.map ((T.obj M).map ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app K)) := by
  simpa only [unboundedEtaleLowerShriekCompIso, projectionMap,
    rightDerivedLowerShriek, rightDerivedLowerShriekIso] using
    projectionMap_compactification_comp A f g
    (HasCompactification.compactification f)
    (HasCompactification.compactification g)
    (HasCompactification.compactification (f ≫ g))
    ((HasCompactification.compactification (f ≫ g)).ofComp
      (HasCompactification.compactification g)) M K

-- Normalize the two tensor conventions without unfolding the derived functors.
private theorem compactSupportProjectionMap_comp_forward
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact (f ≫ g)]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    compactSupportProjectionMap A g
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        (compactSupportProjectionMap A f M
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K)) ≫
      (unboundedEtaleLowerShriekCompIso A f g).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
            ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))).obj M) =
    ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
        ((unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫
      compactSupportProjectionMap A (f ≫ g) M K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((unboundedEtaleUpperStarCompIso A f g).hom.app K)).app M) := by
  have h := tensor_projection_conjugation (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g) (rightDerivedLowerShriek (ModuleCat.{u + 1} A)
    (f ≫ g)) (derivedTensor (ModuleCat.{u + 1} A) X) (derivedTensor (ModuleCat.{u + 1} A) Y)
    (derivedTensor (ModuleCat.{u + 1} A) Z)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) X)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) Y)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) Z)
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor) ((upperStar (ModuleCat.{u + 1} A)
      f).mapDerivedCategory) ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor) ((upperStar
      (ModuleCat.{u + 1} A) g).mapDerivedCategory) ((upperStar (ModuleCat.{u + 1} A) (f ≫
      g)).leftDerivedFunctor) ((upperStar (ModuleCat.{u + 1} A) (f ≫ g)).mapDerivedCategory)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (f ≫ g))
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g) (unboundedEtaleUpperStarCompIso A f g)
      (unboundedEtaleLowerShriekCompIso A f g) M K (((projectionMap (ModuleCat.{u + 1} A) f).app
      M).app (((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor).obj K)) (((projectionMap
      (ModuleCat.{u + 1} A) f).app M).app (((upperStar (ModuleCat.{u + 1} A)
      g).mapDerivedCategory).obj K)) (((projectionMap (ModuleCat.{u + 1} A) g).app
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M)).app K) (((projectionMap
      (ModuleCat.{u + 1} A) (f ≫ g)).app M).app K)
    (((projectionMap (ModuleCat.{u + 1} A) f).app M).naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).hom.app K))
    (pullback_comparison_comp A f g K) (projectionMap_chosen_comp A f g M K)
  have eg : compactSupportProjectionMap A g ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
    M) K =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).hom.app K).app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).obj ((rightDerivedLowerShriek
            (ModuleCat.{u + 1} A) f).obj M)) ≫ (((projectionMap (ModuleCat.{u + 1} A) g).app
            ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M)).app K) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map (((derivedTensor (ModuleCat.{u + 1} A)
          Y).obj ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M)).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).hom.app K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map (((derivedTensorSymmetry (ModuleCat.{u
          + 1} A) Y).inv.app
          (((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory).obj K)).app
            ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M)) := by
    exact compactSupportProjectionMap_eq A g ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
      M) K
  have ef : compactSupportProjectionMap A f M (((upperStar (ModuleCat.{u + 1} A)
    g).mapDerivedCategory).obj K) =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Y).hom.app
          (((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory).obj K)).app
            ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) ≫ (((projectionMap
            (ModuleCat.{u + 1} A) f).app M).app (((upperStar (ModuleCat.{u + 1} A)
            g).mapDerivedCategory).obj K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (((derivedTensor (ModuleCat.{u + 1} A)
          X).obj M).map ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app
          (((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory).obj K))) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).map (((derivedTensorSymmetry (ModuleCat.{u
          + 1} A) X).inv.app
          (((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory).obj (((upperStar (ModuleCat.{u +
            1} A) g).mapDerivedCategory).obj K))).app M) := by
    exact compactSupportProjectionMap_eq A f M (((upperStar (ModuleCat.{u + 1} A)
      g).mapDerivedCategory).obj K)
  have eh : compactSupportProjectionMap A (f ≫ g) M K =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).hom.app K).app ((rightDerivedLowerShriek
        (ModuleCat.{u + 1} A) (f ≫ g)).obj M) ≫
        (((projectionMap (ModuleCat.{u + 1} A) (f ≫ g)).app M).app K) ≫ (rightDerivedLowerShriek
          (ModuleCat.{u + 1} A) (f ≫ g)).map (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
          ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (f ≫ g)).hom.app K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map (((derivedTensorSymmetry
          (ModuleCat.{u + 1} A) X).inv.app
          (((upperStar (ModuleCat.{u + 1} A) (f ≫ g)).mapDerivedCategory).obj K)).app M) := by
    exact compactSupportProjectionMap_eq A (f ≫ g) M K
  have hL := congrArg₂ (fun x y ↦ x ≫ (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map y ≫
    (unboundedEtaleLowerShriekCompIso A f g).hom.app (((derivedTensor (ModuleCat.{u + 1} A) X).obj
      (((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory).obj (((upperStar (ModuleCat.{u + 1}
      A) g).mapDerivedCategory).obj K))).obj M)) eg ef
  have hR := congrArg (fun x ↦ ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
    ((unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫ x ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map (((derivedTensor (ModuleCat.{u + 1}
      A) X).map ((unboundedEtaleUpperStarCompIso A f g).hom.app K)).app M)) eh
  apply hL.trans
  apply Eq.trans ?_ hR.symm
  simpa only [Category.assoc] using h

end TensorConventionProof

set_option backward.isDefEq.respectTransparency false

/-- Tensor projection maps respect the tower-normalized compact-support compositor.
Source: Stacks Project, Tags 0F7B and 0F7J, with the tensor square of Tag 0E48
(blueprint: lem-amb-shriek-tensor-composition).

Proof: work first with right-hand tensor factors. On the compatible proper/open tower,
paste the cartesian exchange/projection square, the proper projection compositor identity,
and the open tensor compositor identity. The pullback coherence identities identify the
remaining tensor-factor path with the canonical pullback compositor. Transport from that
tower to the chosen compactifications using the already proved projection square for
arbitrary common-refinement comparisons. Finally use naturality of the signed tensor
symmetries and the exact-pullback comparisons to put the coefficient first. Invert the
resulting equality when all three projection arrows are invertible.
-/
theorem compactSupportProjectionMap_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Z) :
    (compactSupportProjectionMap A g
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
        (compactSupportProjectionMap A f M
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K)) ≫
      (unboundedEtaleLowerShriekCompIso A f g).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
            ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))).obj M) =
      ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
        ((unboundedEtaleLowerShriekCompIso A f g).hom.app M) ≫
      compactSupportProjectionMap A (f ≫ g) M K ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
        (((derivedTensor (ModuleCat.{u + 1} A) X).map
          ((unboundedEtaleUpperStarCompIso A f g).hom.app K)).app M)) ∧
    (∀ [IsIso (compactSupportProjectionMap A g
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) K)]
        [IsIso (compactSupportProjectionMap A f M
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))]
        [IsIso (compactSupportProjectionMap A (f ≫ g) M K)],
      (unboundedEtaleLowerShriekCompIso A f g).inv.app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj
            ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj
              ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))).obj M) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          (inv (compactSupportProjectionMap A f M
            ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K))) ≫
        inv (compactSupportProjectionMap A g
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M) K) =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g)).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).map
            ((unboundedEtaleUpperStarCompIso A f g).inv.app K)).app M) ≫
        inv (compactSupportProjectionMap A (f ≫ g) M K) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj K).map
          ((unboundedEtaleLowerShriekCompIso A f g).inv.app M)) := by
  have h := compactSupportProjectionMap_comp_forward A f g M K
  refine ⟨h, ?_⟩
  intro _ _ _
  have hi := inverse_congr h
  simp only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app] at hi
  have ht := NatIso.inv_map_hom_app (derivedTensor (ModuleCat.{u + 1} A) X)
    ((unboundedEtaleUpperStarCompIso A f g).app K) M
  simp only [Iso.app_hom, Iso.app_inv] at ht
  rw [ht] at hi
  simpa only [Category.assoc] using hi

/-- The tensor projection maps commute with all compactification comparisons, including
proper refinements whose open square is not cartesian.
Source: Stacks Project, Tags 0F7B, 0F7D, and 0F7I, with Tag 0E48
(blueprint: lem-amb-shriek-tensor-composition).

Proof: apply the already proved right-factor compactification-independence projection
square in the reverse direction. Naturality of the signed tensor symmetry moves the
comparison through the initial swap. Naturality of the compactification comparison moves
it through the exact-pullback comparison and final swap. Reassociate the resulting arrows.
-/
theorem compactSupportProjectionMap_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (M : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((rightDerivedLowerShriekOfCompactificationIso A c d).hom.app M) ≫
      compactSupportProjectionMapOfCompactification A d M K =
    compactSupportProjectionMapOfCompactification A c M K ≫
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K)).obj M) := by
  let T := derivedTensor (ModuleCat.{u + 1} A) Y
  let U := derivedTensor (ModuleCat.{u + 1} A) X
  let L := (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor
  let D := (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
  let F := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  let G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d
  let N := (U.obj M).obj (L.obj K)
  let e := rightDerivedLowerShriekOfCompactificationIso A c d
  let pc : (T.obj (F.obj M)).obj K ⟶ F.obj N :=
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K
  let pd : (T.obj (G.obj M)).obj K ⟶ G.obj N :=
    ((projectionMapOfCompactification (ModuleCat.{u + 1} A) d).app M).app K
  have hp : (T.map (e.hom.app M)).app K ≫ pd = pc ≫ e.hom.app N :=
    (projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
      A c d M K).symm
  let S := derivedTensorSymmetry (ModuleCat.{u + 1} A) Y
  let l := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  let q := ((U.obj M).map (l.hom.app K)) ≫
    ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).inv.app (D.obj K)).app M
  have hc : compactSupportProjectionMapOfCompactification A c M K =
      (S.hom.app K).app (F.obj M) ≫ pc ≫ F.map q := by
    dsimp only [compactSupportProjectionMapOfCompactification, q]
    rw [Functor.map_comp]
  have hd : compactSupportProjectionMapOfCompactification A d M K =
      (S.hom.app K).app (G.obj M) ≫ pd ≫ G.map q := by
    dsimp only [compactSupportProjectionMapOfCompactification, q]
    rw [Functor.map_comp]
  rw [hc, hd]
  have hs : (T.obj K).map (e.hom.app M) ≫ (S.hom.app K).app (G.obj M) =
      (S.hom.app K).app (F.obj M) ≫ (T.map (e.hom.app M)).app K :=
    (S.hom.app K).naturality (e.hom.app M)
  have hn : e.hom.app N ≫ G.map q = F.map q ≫ e.hom.app _ :=
    (e.hom.naturality q).symm
  calc
    _ = (S.hom.app K).app (F.obj M) ≫
        ((T.map (e.hom.app M)).app K ≫ pd) ≫ G.map q := by
      rw [← Category.assoc, hs]
      simp only [Category.assoc]
    _ = (S.hom.app K).app (F.obj M) ≫
        (pc ≫ e.hom.app N) ≫ G.map q := by rw [hp]
    _ = _ := by
      rw [Category.assoc, Category.assoc, hn]
      simp only [Category.assoc]
      rfl

end AlgebraicGeometry.Etale
