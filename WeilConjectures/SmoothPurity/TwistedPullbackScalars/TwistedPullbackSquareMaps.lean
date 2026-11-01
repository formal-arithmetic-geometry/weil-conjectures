/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SchemeGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import WeilConjectures.SixFunctors.Orientation.OrientationIntegralCoefficientTwists
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChange
public import WeilConjectures.SmoothPurity.Supporting.SignedTwistReductionComparison
public import WeilConjectures.SixFunctors.CanonicalTate.CanonicalTateScalarComparisons
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.PuritySourceTransports
public import WeilConjectures.DeligneLaumon.FieldWeilShriekShiftData
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
public import WeilConjectures.SmoothPurity.Pur.PurAdicReconstruction
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralOperationShiftData
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Compact.CompactSupportTermHomFinite
public import WeilConjectures.Mathlib.CategoryTheory.CofilteredSystem
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistDerivedScalarCanonical
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SmoothPurity.Supporting.TwistPreservesFiniteness
public import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonDefinitions
public import WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison

/-! # Scalar squares of twisted pullbacks

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, base-change coherence
(blueprint: def-pur-twisted-pullback-square-maps).
The raw framework rationalization is used as coordinates for the raw PBC category.
All maps below retain the integral, roots-induced normalizations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing Tate twist followed by the even shift, without changing its tensor order.
Source: purity transport, D_W (blueprint: def-pur-twisted-pullback-square-maps). -/
def D (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)] (d : ℕ) :=
  sfRationalTwistingFunctor l E W (d : ℤ) ⋙ shiftFunctor _ (2 * (d : ℤ))

/-- Twisted pullback H_h = D Lh*. Source: purity transport
(blueprint: def-pur-twisted-pullback-square-maps). -/
def H {X Y : Scheme.{u}} (h : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ) :=
  rationalDerivedPullback l E h ⋙ D l E X d

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L)

/-- The specified raw scalar functor in strict-tower coordinates. Source: scalar extension
and its presentation transport (blueprint: def-pur-twisted-pullback-square-maps). -/
abbrev T (W : Scheme.{u}) :=
  sfRationalScalarExtension l E W 0 (Fact.out : l.Prime).ne_zero L i

/-- Canonical scalar/twist/shift comparison, retaining the root-line scalar map.
Source: purity transport, q (blueprint: def-pur-twisted-pullback-square-maps). -/
def q (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)] (d : ℕ)
    (M : sfRationalConstructibleCategory l E W) :
    (T l E L i W).obj ((D l E W d).obj M) ≅
      (D l L W d).obj ((T l E L i W).obj M) :=
  (Functor.commShiftIso (T l E L i W)
      (self := RationalSmoothPurityCanonical.scalarShift l E L i W)
      (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      ((rationalTensorScalarComparison l E L i W).app
        (M, sfRationalTwistingCoefficient l E W (d : ℤ)) ≪≫
        (rationalDerivedTensor l L W).mapIso
          (Iso.prod (Iso.refl _) (CanonicalTate.rationalScalarLine l E L i W d)))

/-- The specified scalar/pullback comparison, already localized from the integral one.
Source: purity transport, p (blueprint: def-pur-twisted-pullback-square-maps). -/
def p {X Y : Scheme.{u}} (h : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : sfRationalConstructibleCategory l E Y) :=
  (rationalPullbackScalarComparison l E L i h).app M

/-- The displayed composite defining a; there is no independently chosen rescaling.
Source: purity transport, a (blueprint: def-pur-twisted-pullback-square-maps). -/
def a {X Y : Scheme.{u}} (h : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (M : sfRationalConstructibleCategory l E Y) :=
  q l E L i X d ((rationalDerivedPullback l E h).obj M) ≪≫
    (D l L X d).mapIso (p l E L i h M)

variable {X X' Y Y' : Scheme.{u}}
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]

/-- U_R, with ordinary contravariant functor order. Source: purity transport
(blueprint: def-pur-twisted-pullback-square-maps). -/
def U (u : X' ⟶ X) (f : X ⟶ Y) :=
  rationalDerivedPullback l E f ⋙ rationalDerivedPullback l E u

/-- V_R. Source: purity transport
(blueprint: def-pur-twisted-pullback-square-maps). -/
def V (f' : X' ⟶ Y') (v : Y' ⟶ Y) :=
  rationalDerivedPullback l E v ⋙ rationalDerivedPullback l E f'

/-- The composite scalar comparison P_U. Source: purity transport
(blueprint: def-pur-twisted-pullback-square-maps). -/
def PU (u : X' ⟶ X) (f : X ⟶ Y)
    (K : sfRationalConstructibleCategory l E Y) :=
  p l E L i u ((rationalDerivedPullback l E f).obj K) ≪≫
    (rationalDerivedPullback l L u).mapIso (p l E L i f K)

/-- r_A. Source: purity transport
(blueprint: def-pur-twisted-pullback-square-maps). -/
def rA (u : X' ⟶ X) (f : X ⟶ Y) (d : ℕ)
    (K : sfRationalConstructibleCategory l E Y) :=
  p l E L i u ((H l E f d).obj K) ≪≫
    (rationalDerivedPullback l L u).mapIso (a l E L i f d K)

/-- r_B. Source: purity transport
(blueprint: def-pur-twisted-pullback-square-maps). -/
def rB (f' : X' ⟶ Y') (v : Y' ⟶ Y) (d : ℕ)
    (K : sfRationalConstructibleCategory l E Y) :=
  a l E L i f' d ((rationalDerivedPullback l E v).obj K) ≪≫
    (H l L f' d).mapIso (p l E L i v K)

end WeilConjectures.TwistedPullbackScalars
