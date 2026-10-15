/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyClass

public import Sheaf.AlgebraicGeometry.CartesianChartRawTransport
public import Sheaf.AlgebraicGeometry.RestrictedOverAbelianComplexData
public import Sheaf.AlgebraicGeometry.CartesianHigherImageChartSystem

/-! # Canonical pullback of chart classes

Source: Stacks Project, Tag 0EYM, the stage-to-apex compatibility square.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The derived inverse-image action on a class with a pulled-back source.
All factors are the canonical composition, single and shift comparisons.
Source: Stacks Project, Tags 03CB and 0EYM.
(blueprint: def-sc-cartesian-chart-class-pullback-core). -/
@[irreducible]
noncomputable def cartesianChartClassPullbackCore {B T T' : Scheme.{u}}
    (h : T ⟶ B) (a : T' ⟶ T) (s : T' ⟶ B) (hs : s = a ≫ h)
    (M : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{u + 1}]).obj M) ⟶ K⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((s)^*[AddCommGrpCat.{u + 1}]).obj M) ⟶
        ((D+((a)^*[AddCommGrpCat.{u + 1}])).obj K)⟦q⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} a h s hs).hom.app M) ≫
    (((a)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    (D+((a)^*[AddCommGrpCat.{u + 1}])).map z ≫
    (D+((a)^*[AddCommGrpCat.{u + 1}]).commShiftIso q).hom.app K

/-- Pull back a chart class, with the free-sheaf source transported from a given
pullback test object. All factors are the specified composition, single-functor,
and shift comparisons of exact inverse image.
Source: Stacks Project, Tags 03CB and 0EYM.
(blueprint: def-sc-cartesian-chart-class-pullback). -/
noncomputable def cartesianChartClassPullback {B T T' : Scheme.{u}}
    (a : T ⟶ B) (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (V : B.Etale) (U : T'.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)) ⟶ K⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((abelianComparisonFree T').obj U) ⟶
      ((D+((b)^*[AddCommGrpCat.{u + 1}])).obj K)⟦q⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      (abelianFreeRepresentablePullbackSquareIso a' V U r hr).hom ≫
    cartesianChartClassPullbackCore a b a' ha ((abelianComparisonFree B).obj V) K q z

/-- The actual stage lift for the chart diagram; it uses the inverse of the
canonical raw cohomology comparison, the chart adjunction, and pullback of the
resulting derived class. No representative or lift is selected by choice.
Source: Stacks Project, Tags 03Q8 and 0EYM.
(blueprint: def-sc-cartesian-chart-cohomology-lift). -/
noncomputable def cartesianChartCohomologyLift
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj ((abelianComparisonFree c.pt.left).obj U) ⟶
      ((D+(((c.π.app j.left).left)^*[AddCommGrpCat.{u + 1}])).obj
        (cartesianDerivedImage f (D.obj j.left).hom
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧ := by
  let h := pullback.snd ((D.map j.hom).left) (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let G := (((pullback.snd ((D.map j.hom).left)
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
  let z := rawRestrictedCohomologyClass h q G V x
  exact cartesianChartClassPullback (D.map j.hom).left (c.π.app j.left).left
    (c.π.app i).left (congrArg (fun t ↦ t.left) (c.w j.hom)).symm V U r hr _ (q : ℤ)
    ((cartesianChartRawAdjunctionIso f (D.obj i).hom (D.map j.hom).left
      (D.obj j.left).hom (Over.w (D.map j.hom)).symm F q V).hom z)

end AlgebraicGeometry.Etale
