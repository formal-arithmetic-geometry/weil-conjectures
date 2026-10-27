/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.OrientationEtaleCoefficientTwists
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-! # Geometric orientation equations
Source: main-20261015 def-sf-orientation, clauses 1--3.
(blueprint: def-sf-orientation-geometric-comparisons).
This is the generic coordinate interface; the owning orientation datum below
pins every comparison to its actual coefficient construction.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Twist coordinates for one of the specified coefficient stages. The object T X d
is the actual coefficient line shifted by 2d. The three isomorphisms are the usual
unit, inverse-image and tensor-power comparisons; their root and coefficient
normalizations are imposed by the full datum below.
Source: comparison conventions in def-sf-orientation
  (blueprint: def-sf-orientation-geometric-comparisons). -/
structure SfOrientationTwists {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (tensor : ∀ X, B X ⥤ B X ⥤ B X)
    (T : ∀ X, ℕ → B X) where
  pull : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (d : ℕ),
    (S.pull f).obj (T Y d) ≅ T X d
  product : ∀ (X : SixFunctorSpace D) (d e : ℕ),
    ((tensor X).obj (T X d)).obj (T X e) ≅ T X (d + e)
  unit : ∀ (X : SixFunctorSpace D) (d : ℕ),
    ((tensor X).obj (T X 0)).obj (T X d) ≅ T X d

/-- Canonical projection and compact-support exchange in operation coordinates.
The normalization fields in the full datum identify these with the datum's A2
and A3 maps. Neither a smooth exceptional-base-change isomorphism nor a tensor
purity isomorphism occurs here.
Source: the definitions of theta and beta (blueprint: def-sf-orientation-geometric-comparisons). -/
structure SfOrientationExchange {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    (S : SixFunctorPushStage D B) (tensor : ∀ X, B X ⥤ B X ⥤ B X)
    (T : ∀ X, ℕ → B X) where
  projection : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (r : ℕ) [SmoothOfRelativeDimension r f.hom.left]
    (c : Compactification f.hom.left) (d : ℕ),
    ((tensor Y).obj ((S.support f c).obj ((S.exceptional f c).obj (T Y 0)))).obj (T Y d) ≅
      (S.support f c).obj
        (((tensor X).obj ((S.exceptional f c).obj (T Y 0))).obj
          ((S.pull f).obj (T Y d)))
  exchange : ∀ (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.g.hom.left] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.f'.hom.left] (r : ℕ)
    [SmoothOfRelativeDimension r Q.f.hom.left]
    [SmoothOfRelativeDimension r Q.f'.hom.left],
    (S.pull Q.g).obj ((S.support Q.f Q.compactification).obj
      ((S.exceptional Q.f Q.compactification).obj (T Q.Y 0))) ≅
      (S.support Q.f' Q.compactification').obj ((S.pull Q.g').obj
        ((S.exceptional Q.f Q.compactification).obj (T Q.Y 0)))

/-- The tensor map, in the order omega tensor pullback. It is the transpose of
inverse projection, counit tensor identity, and the coefficient unitor. The
source convention with pullback first is its composite with symmetry.
Source: displayed theta formula (blueprint: def-sf-orientation-geometric-comparisons). -/
def sfOrientationTheta {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {tensor : ∀ X, B X ⥤ B X ⥤ B X}
    {T : ∀ X, ℕ → B X} (A : SfOrientationTwists S tensor T)
    (P : SfOrientationExchange S tensor T) {X Y : SixFunctorSpace D}
    (f : X ⟶ Y) [IsSeparated f.hom.left]
    (r : ℕ) [SmoothOfRelativeDimension r f.hom.left]
    (c : Compactification f.hom.left) (d : ℕ) :
    ((tensor X).obj ((S.exceptional f c).obj (T Y 0))).obj
        ((S.pull f).obj (T Y d)) ⟶ (S.exceptional f c).obj (T Y d) :=
  (S.exceptionalAdjunction f c).homEquiv _ _
    ((P.projection f r c d).inv ≫
      ((tensor Y).map ((S.exceptionalAdjunction f c).counit.app (T Y 0))).app (T Y d) ≫
      (A.unit Y d).hom)

/-- The dualizing base-change map is the counit transpose of inverse compact-support
exchange, the pulled-back counit, and the pullback-unit identification.
Source: displayed beta formula (blueprint: def-sf-orientation-geometric-comparisons). -/
def sfOrientationBeta {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {tensor : ∀ X, B X ⥤ B X ⥤ B X}
    {T : ∀ X, ℕ → B X} (A : SfOrientationTwists S tensor T)
    (P : SfOrientationExchange S tensor T) (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.g.hom.left] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.f'.hom.left] (r : ℕ)
    [SmoothOfRelativeDimension r Q.f.hom.left]
    [SmoothOfRelativeDimension r Q.f'.hom.left] :
    (S.pull Q.g').obj ((S.exceptional Q.f Q.compactification).obj (T Q.Y 0)) ⟶
      (S.exceptional Q.f' Q.compactification').obj (T Q.Y' 0) :=
  (S.exceptionalAdjunction Q.f' Q.compactification').homEquiv _ _
    ((P.exchange Q r).inv ≫
      (S.pull Q.g).map
        ((S.exceptionalAdjunction Q.f Q.compactification).counit.app (T Q.Y 0)) ≫
      (A.pull Q.g 0).hom)

/-- The coherent geometric part of the orientation family, with compactification
coordinates retained. All maps are isomorphisms in the coefficient derived category.
The composition comparison is the unique mate of compact-support composition.
Source: clauses 1 and 2 of def-sf-orientation
  (blueprint: def-sf-orientation-geometric-comparisons). -/
structure SfGeometricOrientation {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {S : SixFunctorPushStage D B} {tensor : ∀ X, B X ⥤ B X ⥤ B X}
    {T : ∀ X, ℕ → B X} (A : SfOrientationTwists S tensor T)
    (P : SfOrientationExchange S tensor T) where
  component : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left),
    T X d ≅ (S.exceptional f c).obj (T Y 0)
  compactification : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c c' : Compactification f.hom.left),
    component f d c ≪≫ (S.exceptionalComparison f c c').app (T Y 0) =
      component f d c'
  baseChange : ∀ (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.g.hom.left] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.f'.hom.left] (d : ℕ)
    [SmoothOfRelativeDimension d Q.f.hom.left]
    [SmoothOfRelativeDimension d Q.f'.hom.left],
    (component Q.f' d Q.compactification').hom =
      (A.pull Q.g' d).inv ≫
        (S.pull Q.g').map (component Q.f d Q.compactification).hom ≫ sfOrientationBeta A P Q d
  composition : ∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [IsSeparated g.hom.left]
    [IsSeparated (f ≫ g).hom.left] (d e : ℕ)
    [SmoothOfRelativeDimension d f.hom.left] [SmoothOfRelativeDimension e g.hom.left]
    [SmoothOfRelativeDimension (d + e) (f ≫ g).hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left),
    (component (f ≫ g) (d + e) cfg).hom =
      (A.product X d e).inv ≫
        ((tensor X).obj (T X d)).map (A.pull f e).inv ≫
        ((tensor X).map (component f d cf).hom).app ((S.pull f).obj (T Y e)) ≫
        sfOrientationTheta A P f d cf e ≫ (S.exceptional f cf).map (component g e cg).hom ≫
        (sixFunctorExceptionalComposition S f g cf cg cfg).inv.app (T Z 0)

/-- Transported comparison coordinates for localization or finite-stage inclusion.
The unit, pull and tensor comparisons are prescribed by A5; the exchange arrows
remain the target stage's A2 and A3 maps. This record adds no free comparison.
Source: coefficient comparisons in clause 3
  (blueprint: def-sf-orientation-geometric-comparisons). -/
structure SfOrientationImageCoordinates {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {tensor : ∀ X, B X ⥤ B X ⥤ B X} {tensor' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {T : ∀ X, ℕ → B X} (A : SfOrientationTwists S tensor T)
    {L : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' L)
    (ex : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S tensor Q)
    (ex' : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData S' tensor' Q)
    (comparison : ∀ Q : SixFunctorCompactifiedSquare D,
      SixFunctorExchangeComparison (ex Q) (ex' Q) L C) where
  twists : SfOrientationTwists S' tensor' (fun X d ↦ (L X).obj (T X d))
  exchange : SfOrientationExchange S' tensor' (fun X d ↦ (L X).obj (T X d))
  pull_normalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (d : ℕ),
    twists.pull f d = ((C.directAdjunction f).left.app (T Y d)).symm ≪≫
      (L X).mapIso (A.pull f d)
  product_normalization : ∀ (Q : SixFunctorCompactifiedSquare D) (d e : ℕ),
    twists.product Q.X d e =
      (((comparison Q).tensor Q.X).app (T Q.X d, T Q.X e)).symm ≪≫
        (L Q.X).mapIso (A.product Q.X d e)
  unit_normalization : ∀ (X : SixFunctorSpace D) (d : ℕ),
    twists.unit X d = twists.product X 0 d ≪≫
      eqToIso (congrArg (fun i ↦ (L X).obj (T X i)) (Nat.zero_add d))
  projection_normalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.f.hom.left] (r : ℕ)
    [SmoothOfRelativeDimension r Q.f.hom.left] (d : ℕ),
    HEq (exchange.projection Q.f r Q.compactification d).hom
      ((ex' Q).projectionComponent
        ((S'.exceptional Q.f Q.compactification).obj ((L Q.Y).obj (T Q.Y 0)))
        ((L Q.Y).obj (T Q.Y d)))
  exchange_normalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.g.hom.left] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.f'.hom.left] (r : ℕ)
    [SmoothOfRelativeDimension r Q.f.hom.left]
    [SmoothOfRelativeDimension r Q.f'.hom.left],
    HEq (exchange.exchange Q r).hom ((ex' Q).stage.compactExchange.app
      ((S'.exceptional Q.f Q.compactification).obj ((L Q.Y).obj (T Q.Y 0))))

/-- The coefficient-compatibility equation w C(gamma) = gamma' t, with the
exceptional comparison of A5 and the prescribed coefficient-unit comparison.
Source: clause 3 (blueprint: def-sf-orientation-geometric-comparisons). -/
def SfOrientationCoefficientCompatible {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
    {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
    {tensor : ∀ X, B X ⥤ B X ⥤ B X} {tensor' : ∀ X, B' X ⥤ B' X ⥤ B' X}
    {T : ∀ X, ℕ → B X} {T' : ∀ X, ℕ → B' X}
    {A : SfOrientationTwists S tensor T} {A' : SfOrientationTwists S' tensor' T'}
    {P : SfOrientationExchange S tensor T} {P' : SfOrientationExchange S' tensor' T'}
    (o : SfGeometricOrientation A P) (o' : SfGeometricOrientation A' P')
    {L : ∀ X, B X ⥤ B' X} (C : SixFunctorCoefficientComparison S S' L)
    (t : ∀ (X : SixFunctorSpace D) (d : ℕ), (L X).obj (T X d) ≅ T' X d) : Prop :=
  ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left),
    (L X).map (o.component f d c).hom ≫
      (C.supportAdjunction f c).right.hom.app (T Y 0) ≫
      (S'.exceptional f c).map (t Y 0).hom = (t X d).hom ≫ (o'.component f d c).hom


end WeilConjectures
