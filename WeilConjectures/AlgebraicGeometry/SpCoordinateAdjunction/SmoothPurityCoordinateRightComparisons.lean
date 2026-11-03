/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateTensorComparisons
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Kummer.PurityFiniteKummerLevel
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.SmoothPurity.AmbTateRootProjectionReduction
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootTowerFiniteTensor

/-! # Ordered coordinate adjunctions on ordinary derived towers

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels
(blueprint: def-sp-coordinate-right-comparisons).

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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v v' w w' z z'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The original coordinate realization of a right-functor comparison.
Source: Local pairs, cancellation of the common realization
(blueprint: def-sp-coordinate-right-comparisons). -/
def composeRight (b : SpTowerShriek.Base l E)
    (q : SpTowerCalculus.Coordinates l E b) {X T Y : Scheme.{u}}
    (G : SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E T)
    (H : SpTowerShriek.D l E T ⥤ SpTowerShriek.D l E X)
    (R : SpTowerShriek.D l E Y ⥤ SpTowerShriek.D l E X) (a : G ⋙ H ≅ R) :=
  SpTowerCalculus.composeTransport l E b q G H ≪≫ transportedIso l E b q a

/-- The identity on each pullback section, followed by the specified tensor
comparison, identifies an iterated right factor with its chart normal form.
Source: Local pairs, successive pulled-back Tate factors
(blueprint: def-sp-coordinate-right-comparisons). -/
structure PullTwist (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) {X T Y : Scheme.{u}}
    (e : X ⟶ T) (p : T ⟶ Y) (wT : SpChartAdmissibility.Twists l E T)
    (wX : SpChartAdmissibility.Twists l E X) (d : ℕ) where
  ordinary : (o.geometry e).pull.obj (wT.tower d) ≅ wX.tower d
  comparison : projectionRight l E b o p wT d ⋙
    SpTowerShriek.pull l E b (o.geometry e) ≅ chartRight l E b o e p wX d
  normalization : ∀ K : SpTowerShriek.D l E Y,
    comparison.app K =
      ((SpTowerShriek.pull l E b (o.geometry e)).commShiftIso (2 * (d : ℤ))).app
        ((SpTowerShriek.tensor l E b T).obj
          ((SpTowerShriek.pull l E b (o.geometry p)).obj K, line l E wT d)) ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        (((o.geometry e).tensorPullback.app
          ((SpTowerShriek.pull l E b (o.geometry p)).obj K, line l E wT d)) ≪≫
          (SpTowerShriek.tensor l E b X).mapIso (Iso.prod (Iso.refl _)
            (((o.geometry e).pull.mapDerivedCategorySingleFunctor 0).app
              (wT.tower d) ≪≫
                (DerivedCategory.singleFunctor (SpTowerShriek.S l E X) 0).mapIso ordinary)))

/-- Finite Kummer identification of the actual ell-power line, fixed by the root
projection and multiplication of the two coefficient scalars. The ramification
transport is Base.ideals. Source: Local pairs, finite Kummer identification
(blueprint: def-sp-coordinate-right-comparisons). -/
structure RootLines (T : Scheme.{u}) where
  iso : ∀ n : ℕ, spEllTwistOne l E T n ≅ SpTowerClasses.finiteLine l E T n
  normalized : ∀ (n : ℕ) (U : T.ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E T n).obj.obj U)
    (b : (purTwistIntegralConstant T l E).obj.obj U)
    (x : (purTwistZlOne T l).obj.obj U),
    (iso n).hom.val.app U
      (SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (spEllTwistQuotient l E T n) (purTwistIntegralOne T l E) U a
          (purTwistIntegralTensor T l E U b x)) =
      Scheme.tateFiniteTensor T l (SpTowerClasses.FiniteRing l E n) n
        (SpTowerClasses.finiteScalar l E n) U.unop
        (a * (spEllTwistQuotient l E T n).hom.app U b)
        ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime))
          (op n)).hom.app U x)

/-- Evaluate the ordinary adjunct of a line pullback in the specified finite-line
coordinates. This definition uses the actual ordinary adjunction, before deriving.
Source: strict Tate pullback (blueprint: def-sp-coordinate-right-comparisons). -/
def pullSection {b : SpTowerShriek.Base l E} {o : SpTowerShriek.Operations l E b}
    {X T Y : Scheme.{u}} {e : X ⟶ T} {p : T ⟶ Y}
    {wT : SpChartAdmissibility.Twists l E T} {wX : SpChartAdmissibility.Twists l E X}
    {d : ℕ} (a : PullTwist l E b o e p wT wX d) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (spEllTwistLine l E T n d).val.obj U) :=
  ((proEtaleConstantRingPushforward (SpTowerShriek.R l E n) e).map
    (wX.level n d).hom).val.app U
      (SpTowerClasses.adjointSection l E (o.geometry e) a.ordinary.hom n U
        ((wT.level n d).inv.val.app U x))

/-- The canonical component for one further ordered coordinate. It pulls the old
line first, moves its even shift, reassociates the actual derived tensor, multiplies
Tate factors and adds the shifts. Source: Local pairs, ordered iteration
(blueprint: def-sp-coordinate-right-comparisons). -/
def stepComponent (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {k : Type u} [Field k] (w : TwistFamily l E k) (Y : Scheme.{u})
    [Y.Over (Spec (.of k))] (d : ℕ)
    (a : PullTwist l E b o (AffineSpace PUnit.{u + 1} (space Y d) ↘ space Y d)
      (proj Y d) (w (space Y d)) (w (space Y (d + 1))) d)
    (mu : Products l E b (w (space Y (d + 1))))
    (sh : TensorShifts l E b (space Y (d + 1))) (K : SpTowerShriek.D l E Y) :
    ((projectionRight l E b o (proj Y d) (w (space Y d)) d ⋙
      projectionRight l E b o (AffineSpace PUnit.{u + 1} (space Y d) ↘ space Y d)
        (w (space Y (d + 1))) 1).obj K) ≅
    (projectionRight l E b o (proj Y (d + 1)) (w (space Y (d + 1))) (d + 1)).obj K :=
  (shiftFunctor _ (2 : ℤ)).mapIso
    ((SpTowerShriek.tensor l E b (space Y (d + 1))).mapIso
      (Iso.prod (a.comparison.app K) (Iso.refl _)) ≪≫
      sh.first _ _ (2 * (d : ℤ)) ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso
        ((b.calculus (space Y (d + 1))).closed.monoidal.associator _ _ _ ≪≫
          (SpTowerShriek.tensor l E b (space Y (d + 1))).mapIso
            (Iso.prod ((o.comp
              (AffineSpace PUnit.{u + 1} (space Y d) ↘ space Y d)
              (proj Y d)).app K) (mu.derived d 1)))) ≪≫
    (shiftFunctorAdd' _ (2 * (d : ℤ)) 2 (2 * ((d + 1 : ℕ) : ℤ)) (by omega)).symm.app _

/-- Equality transport of the normalized projective right functor into the common
calculus. Source: affine-line factor (blueprint: def-sp-coordinate-right-comparisons). -/
def projectiveTensor {b : SpTowerShriek.Base l E}
    {o : SpTowerShriek.Operations l E b} {S : Scheme.{u}}
    (t : ProjectivePresentation l E b o S) :
    t.presentation.G l E ≅
      SpTowerShriek.pull l E b (o.geometry (ProjectiveLine S ↘ S)) ⋙
        Prod.sectL (SpTowerShriek.D l E (ProjectiveLine S))
          ((SpTowerClasses.line l E t.presentation.classes.chernP)⟦(2 : ℤ)⟧) ⋙
          SpTowerShriek.tensor l E b (ProjectiveLine S) := by
  rcases t with ⟨hinv, p, hb, ho, m, a⟩
  cases hb
  cases ho
  exact Iso.refl _

/-- Restriction of the normalized projective-line Tate line to the affine chart.
The finite root formula fixes the scalar and makes this an actual tower comparison.
Source: affine-line factor (blueprint: def-sp-coordinate-right-comparisons). -/
structure AffineRestriction {b : SpTowerShriek.Base l E}
    {o : SpTowerShriek.Operations l E b} {S : Scheme.{u}}
    (t : ProjectivePresentation l E b o S)
    (wA : SpChartAdmissibility.Twists l E (AffineSpace PUnit.{u + 1} S))
    (roots : RootLines l E (AffineSpace PUnit.{u + 1} S))
    (sh : TensorShifts l E b (AffineSpace PUnit.{u + 1} S)) where
  ordinary : (o.geometry (ProjectiveLine.affineChart S)).pull.obj
    (SpTowerClasses.lineModule l E t.presentation.classes.chernP) ≅ wA.tower 1
  ordinary_normalized : ∀ (n : ℕ) (U : (ProjectiveLine S).ProEtᵒᵖ)
    (a : (SpTowerShriek.B l E (ProjectiveLine S) n).obj.obj U)
    (z : (Scheme.proEtaleRootsOfUnitySheaf (ProjectiveLine S) (l ^ (n + 1))).obj.obj U),
    ((proEtaleConstantRingPushforward (SpTowerShriek.R l E n)
      (ProjectiveLine.affineChart S)).map
      ((wA.level n 1).hom ≫ (roots.iso n).hom)).val.app U
        (SpTowerClasses.adjointSection l E (o.geometry (ProjectiveLine.affineChart S))
          ordinary.hom n U
          ((SpTowerClasses.lineEvaluation l E t.presentation.classes.chernP n).inv.val.app U
            (Scheme.tateFiniteTensor (ProjectiveLine S) l (SpTowerClasses.FiniteRing l E n) n
              (SpTowerClasses.finiteScalar l E n) U.unop a z))) =
      Scheme.tateFiniteTensor (AffineSpace PUnit.{u + 1} S) l
        (SpTowerClasses.FiniteRing l E n) n (SpTowerClasses.finiteScalar l E n)
        (SpTowerClasses.chart (ProjectiveLine.affineChart S) U).unop
        ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} (ProjectiveLine.affineChart S)
          CommRingCat.{u + 1} (CommRingCat.of (SpTowerClasses.FiniteRing l E n))).hom.app U a)
        (SpTowerClasses.restrictRoot l (ProjectiveLine.affineChart S) n U z)
  comparison : t.presentation.G l E ⋙
    SpTowerShriek.pull l E b (o.geometry (ProjectiveLine.affineChart S)) ≅
      projectionRight l E b o (AffineSpace PUnit.{u + 1} S ↘ S) wA 1
  normalized : ∀ K : SpTowerShriek.D l E S,
    (SpTowerShriek.pull l E b (o.geometry (ProjectiveLine.affineChart S))).mapIso
        ((projectiveTensor l E t).symm.app K) ≪≫ comparison.app K =
      (o.geometry (ProjectiveLine.affineChart S)).tensorPullback.app
        ((SpTowerShriek.pull l E b (o.geometry (ProjectiveLine S ↘ S))).obj K,
          (SpTowerClasses.line l E t.presentation.classes.chernP)⟦(2 : ℤ)⟧) ≪≫
      (SpTowerShriek.tensor l E b (AffineSpace PUnit.{u + 1} S)).mapIso
        (Iso.prod ((o.comp (ProjectiveLine.affineChart S) (ProjectiveLine S ↘ S)).app K ≪≫
          (eqToIso (congrArg
            (fun f ↦ (SpTowerShriek.pull l E b (o.geometry f)).obj K)
            (ProjectiveLine.affineChart_over S))))
          (((SpTowerShriek.pull l E b (o.geometry (ProjectiveLine.affineChart S))).commShiftIso
            (2 : ℤ)).app (SpTowerClasses.line l E t.presentation.classes.chernP) ≪≫
            (shiftFunctor _ (2 : ℤ)).mapIso
              (((o.geometry (ProjectiveLine.affineChart S)).pull.mapDerivedCategorySingleFunctor
                0).app (SpTowerClasses.lineModule l E t.presentation.classes.chernP) ≪≫
                (DerivedCategory.singleFunctor _ 0).mapIso ordinary))) ≪≫
        sh.second _ _ 2

/-- The specified right evaluation component for the whole chart. It uses only
realization, exact pullback, normalized tensor evaluation and the ordinary shift.
Source: Levels (blueprint: def-sp-coordinate-right-comparisons). -/
def rightEvaluation (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : SpTowerCalculus.Coordinates l E b) {U T Y : Scheme.{u}}
    (e : U ⟶ T) (p : T ⟶ Y) (w : SpChartAdmissibility.Twists l E U) (d n : ℕ)
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y)) :=
  (SpTowerCalculus.levelComparison l E b q U n).inv.app
    ((originalChartRight l E b o q e p w d).obj K) ≫
  (SpTowerShriek.Ev l E U n).map
    (rightRealization l E b q (chartRight l E b o e p w d) K).hom ≫
  ((SpTowerShriek.Ev l E U n).commShiftIso (2 * (d : ℤ))).hom.app
    ((SpTowerShriek.tensor l E b U).obj
      ((SpTowerShriek.pull l E b (o.geometry e)).obj
        ((SpTowerShriek.pull l E b (o.geometry p)).obj
          ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.obj K)), line l E w d)) ≫
  (shiftFunctor _ (2 * (d : ℤ))).map
    (((b.calculus U).tensorEvaluation n).hom.app
      ((SpTowerShriek.pull l E b (o.geometry e)).obj
        ((SpTowerShriek.pull l E b (o.geometry p)).obj
          ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.obj K)), line l E w d) ≫
      ((b.calculus U).levelClosed n).tensor.map
        (Prod.mkHom
          (((o.geometry e).pullEvaluation n).hom.app _ ≫
            (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) e).map
              (((o.geometry p).pullEvaluation n).hom.app _ ≫
                (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) p).map
                  ((SpTowerCalculus.levelComparison l E b q Y n).hom.app K))) (𝟙 _)))

/-- The analogous specified right evaluation for a projection, with one pullback.
Source: Levels (blueprint: def-sp-coordinate-right-comparisons). -/
def projectionEvaluation (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (q : SpTowerCalculus.Coordinates l E b)
    {T Y : Scheme.{u}} (p : T ⟶ Y) (w : SpChartAdmissibility.Twists l E T) (d n : ℕ)
    (K : spDerivedCoefficientTowers l E Y (q.abelian Y)) :=
  (SpTowerCalculus.levelComparison l E b q T n).inv.app
    ((originalProjectionRight l E b o q p w d).obj K) ≫
  (SpTowerShriek.Ev l E T n).map
    (rightRealization l E b q (projectionRight l E b o p w d) K).hom ≫
  ((SpTowerShriek.Ev l E T n).commShiftIso (2 * (d : ℤ))).hom.app
    ((SpTowerShriek.tensor l E b T).obj
      ((SpTowerShriek.pull l E b (o.geometry p)).obj
        ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.obj K), line l E w d)) ≫
  (shiftFunctor _ (2 * (d : ℤ))).map
    (((b.calculus T).tensorEvaluation n).hom.app
      ((SpTowerShriek.pull l E b (o.geometry p)).obj
        ((SpTowerCalculus.realization l E b Y (q.abelian Y)).functor.obj K), line l E w d) ≫
      ((b.calculus T).levelClosed n).tensor.map
        (Prod.mkHom
          (((o.geometry p).pullEvaluation n).hom.app _ ≫
            (proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) p).map
              ((SpTowerCalculus.levelComparison l E b q Y n).hom.app K)) (𝟙 _)))

/-- The zero-coordinate right-functor identification uses only the normalized
ordinary identity pullback, coefficient unit and shift zero.
Source: d=0 (blueprint: def-sp-coordinate-right-comparisons). -/
structure ZeroComparison (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (Y : Scheme.{u}) (w : SpChartAdmissibility.Twists l E Y) where
  tensor : SpTowerP1.TensorData l E b Y
  ordinaryIdentity : (o.geometry (𝟙 Y)).pull ≅ 𝟭 (SpTowerShriek.S l E Y)
  identity_normalized : ∀ (n : ℕ) (M : SpTowerShriek.S l E Y),
    (SpTowerShriek.ev l E Y n).map (ordinaryIdentity.hom.app M) =
      ((o.geometry (𝟙 Y)).ordinaryPullEvaluation n).hom.app M ≫
        (proEtaleStalkIdentityPullback (SpTowerShriek.R l E n) Y).hom.app
          ((SpTowerShriek.ev l E Y n).obj M)
  ordinaryUnit : w.tower 0 ≅ SpTowerClasses.coefficient Y (SpTowerClasses.Arings l E Y)
  unit_normalized : ∀ (n : ℕ) (V : Y.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E Y n).obj (w.tower 0)).val.obj V),
    HEq (((SpTowerShriek.ev l E Y n).map ordinaryUnit.hom).val.app V x)
      ((w.level n 0).hom.val.app V x)

/-- The canonical zero-dimensional component, from its normalized ordinary data.
Source: d=0 (blueprint: def-sp-coordinate-right-comparisons). -/
def ZeroComparison.component {b : SpTowerShriek.Base l E}
    {o : SpTowerShriek.Operations l E b} {Y : Scheme.{u}}
    {w : SpChartAdmissibility.Twists l E Y} (a : ZeroComparison l E b o Y w)
    (K : SpTowerShriek.D l E Y) :
    (projectionRight l E b o (𝟙 Y) w 0).obj K ≅ K :=
  (shiftFunctorZero _ ℤ).app _ ≪≫
    (SpTowerShriek.tensor l E b Y).mapIso
      (Iso.prod
        (((Functor.mapDerivedCategoryNatIso a.ordinaryIdentity) ≪≫
          Functor.mapDerivedCategoryIdIso _).app K)
        ((DerivedCategory.singleFunctor _ 0).mapIso a.ordinaryUnit)) ≪≫
    a.tensor.rightUnit l E K

end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
