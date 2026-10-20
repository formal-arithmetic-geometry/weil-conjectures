/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
import Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality
import all Sheaf.AlgebraicGeometry.CartesianHigherImageFiniteRawAssembly

/-! # Naturality of a finite-stage raw cartesian chart representative

Source: Stacks Project, Tag 0EYM and the exchange comparison of Tags 03CB and 0GIT.
(blueprint: lem-sc-cartesian-raw-class-chart-naturality).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] restrictedOverCohomologyMap
  cartesianDerivedImageMap cartesianChartCohomologyLift cartesianChartCohomologyIso
  upperStar upperStarCompDerivedPlus

set_option backward.isDefEq.respectTransparency true

/-- The finite-stage chart identity propagates to every arrow above the chosen stage.

Source: Stacks Project, Tag 0EYM, with inverse-image composition and raw evaluation
naturality from Tags 03CB and 03Q8. Factor the transition along a.left followed by b
using exchange composition and functoriality of shift. Substitute the base-stage
identity. Chart-lift naturality then identifies the resulting composite with the
restricted-cohomology image of x. This is the transition part only.
(blueprint: lem-sc-cartesian-raw-class-chart-naturality).
-/
theorem cartesianRawClass_chart_naturality
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i j : I) (V : c.pt.left.Etale) [IsAffine V.left]
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj V) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)
    (W : (D.obj j).left.Etale) (_ : IsAffine W.left)
    (r : V.left ⟶ W.left)
    (hr : IsPullback r V.hom W.hom (c.π.app j).left)
    (l : Over j) (b : l.left ⟶ i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj j).hom)
      (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D j).obj l) W)
    (hbase :
      z ≫ (shiftFunctor _ (q : ℤ)).map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
            (c.π.app l.left).left (D.map b).left (c.π.app i).left
            (congrArg (fun t ↦ t.left) (c.w b)).symm).hom.app _ ≫
            (D+(((c.π.app l.left).left)^*[AddCommGrpCat.{u + 1}])).map
              (cartesianDerivedImageMap f (D.obj i).hom (D.obj l.left).hom
                (D.map b).left (Over.w (D.map b)).symm
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) =
        cartesianChartCohomologyLift f D c F q j W V r hr l x) :
      ∀ (m : Over j) (a : m ⟶ l),
        z ≫ (shiftFunctor _ (q : ℤ)).map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
            (c.π.app m.left).left (D.map (a.left ≫ b)).left (c.π.app i).left
            (congrArg (fun t ↦ t.left) (c.w (a.left ≫ b))).symm).hom.app _ ≫
            (D+(((c.π.app m.left).left)^*[AddCommGrpCat.{u + 1}])).map
              (cartesianDerivedImageMap f (D.obj i).hom (D.obj m.left).hom
                (D.map (a.left ≫ b)).left (Over.w (D.map (a.left ≫ b))).symm
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) =
          cartesianChartCohomologyLift f D c F q j W V r hr m
            (restrictedOverCohomologyMap (pullback.snd f (D.obj j).hom)
              (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
              (q : ℤ) ((cartesianChartDiagram f D j).map a) W x) := by
  have _ := hc
  intro m a
  change z ≫ (shiftFunctor _ (q : ℤ)).map
    (rawTransition (i := i) (j := m.left) D c f
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) (a.left ≫ b)) = _
  rw [← rawTransition_comp (i := i) (j := l.left) (k := m.left) D c f
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F) b a.left, Functor.map_comp, ← Category.assoc]
  dsimp only [rawTransition]
  rw [hbase]
  exact cartesianChartCohomologyLift_naturality f D c F q j W V r hr l m a x

end AlgebraicGeometry.Etale
