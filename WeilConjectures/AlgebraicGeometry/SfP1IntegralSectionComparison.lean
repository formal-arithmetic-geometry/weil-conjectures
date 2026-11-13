/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData
import WeilConjectures.AlgebraicGeometry.SfDiagonalSectionForgetSupports
import WeilConjectures.AlgebraicGeometry.SfP1DiagonalLiftProperForget
import WeilConjectures.AlgebraicGeometry.SfP1OrdinarySectionExchange
import WeilConjectures.AlgebraicGeometry.SfP1ProjectionProperForget

/-! # Transport of the diagonal section unit

This equation is independent of any Tate twist, Ext representative or trace.
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale.SfP1Transport

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Functor.mapDerivedCategory AlgebraicGeometry.ProjectiveSpace
  upperStar lowerStar ordinaryFinitePullback ordinaryFinitePushforward
  ordinaryFiniteUnitPullback rightDerivedLowerShriek
  rightDerivedLowerShriekIsoRightDerivedLowerStar derivedTensorUnit

private theorem constantComparison_whole
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (i : X ≅ ProjectiveLine S) :
    constantComparison A i = ordinaryFiniteUnitPullback A i.hom ≪≫ constantUnit A X := by
  unfold constantComparison
  rfl

private theorem cancel_factor
    {C : Type*} [Category C] {P Q R : C}
    (v : P ≅ Q) (c : Q ≅ R) (w : P ≅ R) (hw : w = v ≪≫ c) :
    c.hom ≫ w.inv = v.inv := by
  rw [hw]
  simp only [Iso.trans_inv, Iso.hom_inv_id_assoc]

private theorem inverse_factor
    {C : Type*} [Category C] {P Q R : C}
    (v : P ≅ Q) (c : Q ≅ R) (w : P ≅ R) (hw : w = v ≪≫ c) :
    c.inv ≫ v.inv = w.inv := by
  rw [hw, Iso.trans_inv]

private theorem paste_naturality
    {C D : Type*} [Category C] [Category D]
    {F R : D ⥤ C} (h : F ⟶ R)
    {U T : C} {Y Z W W' : D}
    (s : U ⟶ F.obj Y) (j : Y ⟶ Z) (k : Z ⟶ W) (m : W ⟶ W')
    (b : R.obj W' ⟶ T) :
    s ≫ F.map (j ≫ k ≫ m) ≫ h.app W' ≫ b =
      (s ≫ F.map (j ≫ k) ≫ h.app W) ≫ R.map m ≫ b := by
  rw [← Category.assoc j k m, F.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% h.naturality m]

private theorem compact_prefix
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (a : Bool) :
    diagonalUnit A f a ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).map
          (diagonalLift A f i hi) ≫
        (projectionComparison A f i hi a).hom.app
          ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (ordinaryFiniteUnit A (ProjectiveLine S))) =
      (constantUnit A X).inv ≫ supportedDerivedUnit A (projection f a) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          (supportedDerivedUnit A (TraceDiagonalDatum.diagonal f)) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          ((ordinaryFinitePushforward A (TraceDiagonalDatum.diagonal f)).map
            ((constantUnit A X).hom ≫ (constantComparison A i).inv)) ≫
        (ordinaryFinitePushforward A (projection f a)).map
          ((properExchange A (diagonalSquare f i hi)).inv.app
            (ordinaryFiniteUnit A (ProjectiveLine S))) ≫
        (properExchange A (projectionSquare f i hi a)).inv.app
          ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (ordinaryFiniteUnit A (ProjectiveLine S))) := by
  have hk := diagonalSection_forgetSupports A f a
    ((ordinaryFinitePullback A i.hom).obj (ordinaryFiniteUnit A (ProjectiveLine S)))
    (constantComparison A i).inv
  rewrite [diagonalLift_eq_ordinaryProperForget A f i hi,
    projectionComparison_eq_ordinaryProperForget A f i hi a]
  rewrite [paste_naturality, hk]
  simp only [Category.assoc]

/-- Proper exchange and forget-supports carry the compact-support diagonal section
unit to the ordinary section unit, under an isomorphism over the base. -/
theorem sectionComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (i : X ≅ ProjectiveLine S) (hi : i.hom ≫ (ProjectiveLine S ↘ S) = f)
    (a : Bool) :
    diagonalUnit A f a ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (projection f a)).map
          (diagonalLift A f i hi) ≫
        (projectionComparison A f i hi a).hom.app
          ((ordinaryFinitePushforward A (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (ordinaryFiniteUnit A (ProjectiveLine S))) =
      (constantComparison A i).inv ≫
        (ordinaryFinitePullback A i.hom).map (projectiveLineDiagonalAlpha A S a) := by
  let c := constantUnit A X
  let v := ordinaryFiniteUnitPullback A i.hom
  let w := constantComparison A i
  have hw : w = v ≪≫ c := constantComparison_whole A i
  rewrite [compact_prefix A f i hi a]
  have hc := cancel_factor v c w hw
  rewrite [hc]
  rewrite [ordinarySection_exchange A f i hi a]
  have hw' := inverse_factor v c w hw
  rewrite [reassoc_of% hw']
  rfl

end AlgebraicGeometry.Etale.SfP1Transport
