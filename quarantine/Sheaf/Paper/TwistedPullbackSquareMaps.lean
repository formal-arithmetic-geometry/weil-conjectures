/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.CanonicalTateComparisons
public import Sheaf.Paper.PuritySourceTransports
public import Sheaf.Paper.FieldWeilShriekShiftData
public import Sheaf.Paper.FiniteSmoothPullbackExchange
public import Sheaf.Paper.AdicPurityScalarNaturality
public import Sheaf.Paper.IntegralLineTensorComparisonDefinitions
public import Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison

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

/-- Pullback of the shifted twist, using the actual root-line pullback for arbitrary h.
Source: purity transport, z (blueprint: def-pur-twisted-pullback-square-maps). -/
def z {X Y : Scheme.{u}} (h : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (d : ℕ)
    (M : sfRationalConstructibleCategory l E Y) :
    (rationalDerivedPullback l E h).obj ((D l E Y d).obj M) ≅
      (D l E X d).obj ((rationalDerivedPullback l E h).obj M) :=
  ((rationalDerivedPullback l E h).commShiftIso (2 * (d : ℤ))).app _ ≪≫
    (shiftFunctor _ (2 * (d : ℤ))).mapIso
      (canonicalRationalPullbackTensor l E h M
        (sfRationalTwistingCoefficient l E Y (d : ℤ)) ≪≫
        (rationalDerivedTensor l E X).mapIso
          (Iso.prod (Iso.refl _) (CanonicalTate.rationalPull l E h d)))

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

/-- The square comparison is c_(u,f) inverse followed by c_(f',v), including the
commutativity equality of scheme maps. Source: purity transport, t
(blueprint: def-pur-twisted-pullback-square-maps). -/
def t (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    (sq : u ≫ f = f' ≫ v) : U l E u f ≅ V l E f' v :=
  (fieldRationalPullComp l E u f).symm ≪≫
    eqToIso (by rw [sq]) ≪≫
      fieldRationalPullComp l E f' v

/-- The composite scalar comparison P_U. Source: purity transport
(blueprint: def-pur-twisted-pullback-square-maps). -/
def PU (u : X' ⟶ X) (f : X ⟶ Y)
    (K : sfRationalConstructibleCategory l E Y) :=
  p l E L i u ((rationalDerivedPullback l E f).obj K) ≪≫
    (rationalDerivedPullback l L u).mapIso (p l E L i f K)

/-- P_V is the same specified composite on the other route. Source: purity transport
(blueprint: def-pur-twisted-pullback-square-maps). -/
def PV (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    (K : sfRationalConstructibleCategory l E Y) := PU l E L i f' v K

/-- The twisted square m = D(t) z. Source: purity transport
(blueprint: def-pur-twisted-pullback-square-maps). -/
def m (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    (sq : u ≫ f = f' ≫ v) (d : ℕ) (K : sfRationalConstructibleCategory l E Y) :=
  z l E u d ((rationalDerivedPullback l E f).obj K) ≪≫
    (D l E X' d).mapIso ((t l E u f f' v sq).app K)

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

/-- All five scalar-square equations, including the two intermediate identities.
The equations quantify over objects, hence are component equalities of the natural
comparisons. Source: purity transport, (Z), (C), intermediate identities, (M)
(blueprint: def-pur-twisted-pullback-square-maps). -/
def SquareEquations (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
    (sq : u ≫ f = f' ≫ v) (d : ℕ) : Prop :=
  (∀ M : sfRationalConstructibleCategory l E X,
    (p l E L i u ((D l E X d).obj M)).hom ≫
      (rationalDerivedPullback l L u).map (q l E L i X d M).hom ≫
      (z l L u d ((T l E L i X).obj M)).hom =
    (T l E L i X').map (z l E u d M).hom ≫
      (q l E L i X' d ((rationalDerivedPullback l E u).obj M)).hom ≫
      (D l L X' d).map (p l E L i u M).hom) ∧
  (∀ K : sfRationalConstructibleCategory l E Y,
    (T l E L i X').map ((t l E u f f' v sq).hom.app K) ≫
      (PV l E L i f' v K).hom =
    (PU l E L i u f K).hom ≫
      (t l L u f f' v sq).hom.app ((T l E L i Y).obj K)) ∧
  (∀ K : sfRationalConstructibleCategory l E Y,
    (rA l E L i u f d K).hom ≫
      (z l L u d ((rationalDerivedPullback l L f).obj ((T l E L i Y).obj K))).hom =
    (T l E L i X').map
        (z l E u d ((rationalDerivedPullback l E f).obj K)).hom ≫
      (q l E L i X' d ((U l E u f).obj K)).hom ≫
      (D l L X' d).map (PU l E L i u f K).hom) ∧
  (∀ K : sfRationalConstructibleCategory l E Y,
    (rB l E L i f' v d K).hom =
      (q l E L i X' d ((V l E f' v).obj K)).hom ≫
        (D l L X' d).map (PV l E L i f' v K).hom) ∧
  (∀ K : sfRationalConstructibleCategory l E Y,
    (T l E L i X').map (m l E u f f' v sq d K).hom ≫
      (rB l E L i f' v d K).hom =
    (rA l E L i u f d K).hom ≫
      (m l L u f f' v sq d ((T l E L i Y).obj K)).hom)




end WeilConjectures.TwistedPullbackScalars
