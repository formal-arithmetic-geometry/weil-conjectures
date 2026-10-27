/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.Paper.OrientationEtaleFamily
public import Sheaf.Paper.OrientationGeometricComparisons
public import Sheaf.Paper.OrientationCoefficientTwists

/-!
# Coherent six-functor orientations

Source: main-20261015, sec-six-functors/sk-def-sf-orientation/def-sf-orientation.md
(blueprint: def-sf-orientation-higher-pair).

The two comparison arrows below are counit transposes. In particular, an
orientation never supplies an arbitrary replacement for either arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  sixFunctorCoefficientRational sixFunctorCoefficientTensor
  sixFunctorCoefficientExchange


/-- Integral comparison coordinates. All data are fixed by the displayed actual
root-line maps, A2 and A3. In particular these fields cannot replace canonical
exchange by an arbitrary smooth-purity isomorphism.
Source: theta, beta and the integral coefficient convention
(blueprint: def-sf-orientation-higher-pair). -/
structure SfIntegralOrientationCoordinates {D : FiniteFieldDatum.{u}}
    {C : D.CoefficientDatum} {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E) where
  twists : SfOrientationTwists H.integral H.integralTensor
    (sfOrientationIntegralLineOn D C E)
  exchange : SfOrientationExchange H.integral H.integralTensor
    (sfOrientationIntegralLineOn D C E)
  pull_normalization : ∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) (d : ℕ),
    HEq (twists.pull f d).hom.hom
      (sfOrientationIntegralPullOn D C E f d)
  product_normalization : ∀ (X : SixFunctorSpace D) (d e : ℕ),
    HEq (twists.product X d e).hom.hom
      (sfOrientationIntegralProductOn D C E X d e)
  unit_normalization : ∀ (X : SixFunctorSpace D) (d : ℕ),
    twists.unit X d = twists.product X 0 d ≪≫
      eqToIso (congrArg (sfOrientationIntegralLineOn D C E X) (Nat.zero_add d))
  projection_normalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.f.hom.left] (r : ℕ)
    [SmoothOfRelativeDimension r Q.f.hom.left] (d : ℕ),
    HEq (exchange.projection Q.f r Q.compactification d).hom
      ((H.integralExchange Q).projectionComponent
        ((H.integral.exceptional Q.f Q.compactification).obj
          (sfOrientationIntegralLineOn D C E Q.Y 0))
        (sfOrientationIntegralLineOn D C E Q.Y d))
  exchange_normalization : ∀ (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.g.hom.left] [IsSeparated Q.f.hom.left]
    [IsSeparated Q.f'.hom.left] (r : ℕ)
    [SmoothOfRelativeDimension r Q.f.hom.left]
    [SmoothOfRelativeDimension r Q.f'.hom.left],
    HEq (exchange.exchange Q r).hom
      ((H.integralExchange Q).stage.compactExchange.app
        ((H.integral.exceptional Q.f Q.compactification).obj
          (sfOrientationIntegralLineOn D C E Q.Y 0)))



/-- Integral and rational geometric families at a finite coefficient field.
Rationalization is compared only in its defined direction, integral to rational.
Source: all higher coefficient components and clauses 1--3
(blueprint: def-sf-orientation-higher-pair). -/
structure SfHigherOrientation {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E) where
  integralCoordinates : SfIntegralOrientationCoordinates H
  integral : SfGeometricOrientation integralCoordinates.twists integralCoordinates.exchange
  rationalCoordinates : SfOrientationImageCoordinates (tensor' := H.rationalTensor)
    integralCoordinates.twists
    H.rationalization H.integralExchange H.rationalExchange H.rationalExchangeComparison
  rational : SfGeometricOrientation rationalCoordinates.twists rationalCoordinates.exchange
  rationalization : SfOrientationCoefficientCompatible integral rational H.rationalization
    (fun _ _ ↦ Iso.refl _)






end WeilConjectures
