/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons

/-! # Normalized root and tensor foundations

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels
(blueprint: lem-sp-coordinate-foundations).

All levels n denote exponent n+1. The full subcategories below have uniform bounds,
without normalization. Every arrow belongs to an ordinary derived tower category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v v' w w' z z'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The normalized ordinary root/tensor comparisons, projective presentations and
admissible domains used before forming any affine or chart adjunction.
Source: latest blueprint, Local pairs, and the original coordinate node steps 1--4.
(blueprint: lem-sp-coordinate-foundations). -/
structure Foundations (k : Type u) [Field k] (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    (w : TwistFamily l E k) where
  projective : ∀ Y : Bases k, ProjectivePresentation l E b o Y.val.left
  roots : ∀ Y : Bases k, RootLines l E Y.val.left
  shifts : ∀ Y : Bases k, TensorShifts l E b Y.val.left
  products : ∀ Y : Bases k, Products l E b (w Y.val.left)
  pulled : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d) (r : ℕ),
    PullTwist l E b o e (proj Y.val.left d) (w (space Y.val.left d)) (w U.val.left) r
  _pulled_zero : ∀ (Y U : Bases k) (d n : ℕ)
    (e : U.val.left ⟶ space Y.val.left d) (V : (space Y.val.left d).ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E (space Y.val.left d) n).obj.obj V),
    pullSection l E (pulled Y U d e 0) n V a =
      (Scheme.proEtaleConstantDirectImageMap.{u, u + 2} e CommRingCat.{u + 1}
        (CommRingCat.of (SpTowerClasses.FiniteRing l E n))).hom.app V a
  _pulled_one : ∀ (Y U : Bases k) (d n : ℕ)
    (e : U.val.left ⟶ space Y.val.left d) (V : (space Y.val.left d).ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E (space Y.val.left d) n).obj.obj V)
    (z : (Scheme.proEtaleRootsOfUnitySheaf (space Y.val.left d) (l ^ (n + 1))).obj.obj V),
    ((roots U).iso n).hom.val.app (SpTowerClasses.chart e V)
      (pullSection l E (pulled Y U d e 1) n V
        (((roots (coordinateBase Y d)).iso n).inv.val.app V
          (Scheme.tateFiniteTensor (space Y.val.left d) l (SpTowerClasses.FiniteRing l E n) n
            (SpTowerClasses.finiteScalar l E n) V.unop a z))) =
      Scheme.tateFiniteTensor U.val.left l (SpTowerClasses.FiniteRing l E n) n
        (SpTowerClasses.finiteScalar l E n) (SpTowerClasses.chart e V).unop
        ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} e CommRingCat.{u + 1}
          (CommRingCat.of (SpTowerClasses.FiniteRing l E n))).hom.app V a)
        (SpTowerClasses.restrictRoot l e n V z)
  _pulled_product : ∀ (Y U : Bases k) (d n r : ℕ)
    (e : U.val.left ⟶ space Y.val.left d) (V : (space Y.val.left d).ProEtᵒᵖ)
    (x : (spEllTwistLine l E (space Y.val.left d) n (r + 1 : ℕ)).val.obj V)
    (y : (spEllTwistOne l E (space Y.val.left d) n).val.obj V),
    pullSection l E (pulled Y U d e (r + 2)) n V
      (SheafOfModules.siteSheafTensorTmul
        (spEllTwistLine l E (space Y.val.left d) n (r + 1 : ℕ))
        (spEllTwistOne l E (space Y.val.left d) n) V x y) =
      SheafOfModules.siteSheafTensorTmul
        (spEllTwistLine l E U.val.left n (r + 1 : ℕ)) (spEllTwistOne l E U.val.left n)
        (SpTowerClasses.chart e V)
        (pullSection l E (pulled Y U d e (r + 1)) n V x)
        (pullSection l E (pulled Y U d e 1) n V y)
  affine : ∀ Y : Bases k, AffineRestriction l E (projective Y)
    (w (space Y.val.left 1)) (roots (coordinateBase Y 1)) (shifts (coordinateBase Y 1))
  affine_source : ∀ (Y : Bases k) (M : (P l E b q (space Y.val.left 1)).FullSubcategory),
    SpTowerP1.domain l E (projective Y).presentation.classes.base (ProjectiveLine Y.val.left)
      ((SpTowerShriek.openD l E b (o.openOp (ProjectiveLine.affineChart Y.val.left))).obj
        ((SpTowerCalculus.realization l E b (space Y.val.left 1)
          (q.abelian (space Y.val.left 1))).functor.obj M.obj))
  affine_target : ∀ (Y : Bases k) (K : (P l E b q Y.val.left).FullSubcategory),
    SpTowerP1.domain l E (projective Y).presentation.classes.base Y.val.left
      ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj K.obj)
  _domains : ∀ (Y : Bases k) (K : (P l E b q Y.val.left).FullSubcategory),
    SpChartAdmissibility.domain l E b Y.val.left
      ((SpTowerCalculus.realization l E b Y.val.left (q.abelian Y.val.left)).functor.obj K.obj)
  step : ∀ (Y : Bases k) (d : ℕ),
    projectionRight l E b o (proj Y.val.left d) (w (space Y.val.left d)) d ⋙
      projectionRight l E b o
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1 ≅
      projectionRight l E b o (proj Y.val.left (d + 1))
        (w (space Y.val.left (d + 1))) (d + 1)
  _step_normalized : ∀ (Y : Bases k) (d : ℕ) (K : SpTowerShriek.D l E Y.val.left),
    (step Y d).app K = stepComponent l E b o w Y.val.left d
      (pulled Y (coordinateBase Y (d + 1)) d
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d) d)
      (products (coordinateBase Y (d + 1))) (shifts (coordinateBase Y (d + 1))) K
  zeroComparison : ∀ Y : Bases k, ZeroComparison l E b o Y.val.left (w Y.val.left)
  zero : ∀ Y : Bases k, 𝟭 (SpTowerShriek.D l E Y.val.left) ≅
    projectionRight l E b o (𝟙 Y.val.left) (w Y.val.left) 0
  zero_normalized : ∀ (Y : Bases k) (K : SpTowerShriek.D l E Y.val.left),
    (zero Y).app K = ((zeroComparison Y).component l E K).symm

  chart_closed : ∀ (Y U : Bases k) (d : ℕ) (e : U.val.left ⟶ space Y.val.left d)
    (_over : e ≫ proj Y.val.left d ≫ Y.val.hom = U.val.hom)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (K : (P l E b q Y.val.left).FullSubcategory),
    P l E b q U.val.left ((originalChartRight l E b o q e (proj Y.val.left d)
      (w U.val.left) d).obj K.obj)

/-- Multiply the ordered right factors recursively, starting from the normalized
coefficient unit. Source: Local pairs, ordered iteration.
(blueprint: lem-sp-coordinate-foundations). -/
def Foundations.iteration {k : Type u} [Field k] {b : SpTowerShriek.Base l E}
    {o : SpTowerShriek.Operations l E b} {q : SpTowerCalculus.Coordinates l E b}
    {w : TwistFamily l E k} (a : Foundations l E k b o q w) (Y : Bases k) :
    ∀ d : ℕ, orderedRight l E b o w Y.val.left d ≅
      projectionRight l E b o (proj Y.val.left d) (w (space Y.val.left d)) d
  | 0 => a.zero Y
  | d + 1 => Functor.isoWhiskerRight (a.iteration Y d)
      (projectionRight l E b o
        (AffineSpace PUnit.{u + 1} (space Y.val.left d) ↘ space Y.val.left d)
        (w (space Y.val.left (d + 1))) 1) ≪≫ a.step Y d

end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
