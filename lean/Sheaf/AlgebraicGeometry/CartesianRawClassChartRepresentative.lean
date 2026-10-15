/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CartesianChartClassPullback
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
import Sheaf.AlgebraicGeometry.AbelianRawPullbackComposition
import Sheaf.AlgebraicGeometry.CartesianChartExchangeNaturality
import Sheaf.AlgebraicGeometry.CartesianHigherImageTransitions
import Sheaf.AlgebraicGeometry.CofilteredAffineEtaleModel
import Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonEvaluationIsIso
import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonIsIso
import Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonNaturality

/-! # Finite-stage chart representatives of raw cartesian classes

Source: Stacks Project, Tags 0EYM, 0EYL and 0GIT.
(blueprint: lem-sc-cartesian-raw-class-chart-representative).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- A raw stage class admits a chart representative after one further base change.

Source: Stacks Project, Tags 0EYL and 0GIT for descent with the original stage
coefficient complex fixed; Tag 0EYM for the exchange comparison square.
(blueprint: lem-sc-cartesian-raw-class-chart-representative).

Proof: Restrict the inverse system to arrows into i and descend the affine test
object to an affine etale model. The resulting models form a limiting qcqs system
with affine transitions. Apply derived cohomology continuity with the fixed
bounded-below complex cartesianDerivedImage f (D.obj i).hom F[0]. The free
representable sections adjunction identifies the given raw class with the
hypercohomology of its pullback to V, so surjectivity gives a representative at
one model. For this identification with arbitrary bounded-below coefficients,
take a bounded-below injective representative: evaluation at the free
representable generator computes its restricted derived sections. Replace the
descended affine model by its base change to the representative's stage and
rename that stage j; it is still affine because the transition is affine.
Apply the stage exchange to that representative. Derived adjunction
and the raw restricted cohomology comparison identify it with x on the
cartesian chart. Let l be the identity object at this new stage, and let b be
its arrow to i. Pasting of exchange maps identifies the limit image of x with
the limit image of z. For any arrow a to l, naturality of restricted cohomology,
derived adjunction, the exact inverse-image single and shift comparisons, and
exchange pasting identify the pullback of x with z followed by the displayed
transition along a.left followed by b. These are equalities of specified maps,
before invoking continuity on the chart system. No zero hypothesis or eventual
vanishing is asserted. The argument also includes empty affine V and q=0.
-/
theorem exists_cartesianRawClass_chart_representative
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (i : I) (V : c.pt.left.Etale) [IsAffine V.left]
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((abelianComparisonFree c.pt.left).obj V) ⟶
        ((D+(((c.π.app i).left)^*[AddCommGrpCat.{u + 1}])).obj
          (cartesianDerivedImage f (D.obj i).hom
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(q : ℤ)⟧)
 :
    ∃ (j : I) (W : (D.obj j).left.Etale) (_ : IsAffine W.left)
      (r : V.left ⟶ W.left)
      (hr : IsPullback r V.hom W.hom (c.π.app j).left)
      (l : Over j) (b : l.left ⟶ i)
      (x : restrictedOverCohomology (pullback.snd f (D.obj j).hom)
        (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
        (q : ℤ) ((cartesianChartDiagram f D j).obj l) W),
      z ≫ (shiftFunctor _ (q : ℤ)).map
          (cartesianDerivedImageMap f (D.obj i).hom c.pt.hom (c.π.app i).left
            (Over.w (c.π.app i)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) =
        (cartesianChartCohomologyIso f (D.obj j).hom (c.π.app j).left c.pt.hom
          (Over.w (c.π.app j)).symm F q W V r hr).hom
          (restrictedOverCohomologyMap (pullback.snd f (D.obj j).hom)
            (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
            (q : ℤ) ((cartesianChartCone f D c j).π.app l) W x) ∧
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
  sorry

end AlgebraicGeometry.Etale
