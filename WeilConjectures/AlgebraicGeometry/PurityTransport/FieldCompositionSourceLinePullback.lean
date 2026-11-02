/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceGeometricData

/-! # Scalar compatibility of a normalized shifted Tate comparison

Source: smooth composition's coefficient passage, root and power calculation.
(blueprint: lem-pur-field-composition-source-line-pullback). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry Scheme
open CategoryTheory.Functor.OplaxMonoidal
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
attribute [local irreducible] DerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

/-- The normalized shifted Tate pullback is compatible with coefficient change.
Source: smooth composition's coefficient passage, pullback part of Step 2.
(blueprint: lem-pur-field-composition-source-line-pullback).

Proof in words. The finite root comparison is fixed by PullNormalized. Its
uniqueness follows by forgetting modules and cancelling the invertible ordinary
pullback-to-comap comparison. Thus the integral_normalized equations for p and
p' give identical finite projections. The inverse-limit hom extensionality
therefore identifies p.integral and p'.integral. Their first_normalized equations
express both first-line pullbacks by scalarPull of this same integral map.
Expand scalarFirst and scalarPull. Associativity of extension of scalars and
coefficientMap_comp, together with hunit, identify the two coefficient/geometric
words; both send a scalar and a pulled root to the same pure tensor. This is
the first-line scalar square. At power zero use the scalar and pullback units.
At successors use the monoidality of the ordinary pullIso and the normalized
balanced scalar tensorator. The power_normalized equations then give the
ordinary square for every exponent e. For exact scalar extension, compare its
derived adjunction unit on a single complex with the single of the ordinary
unit. This identifies scalarLineZero with the canonical single comparison and
the ordinary power map. Compatibility of left derivation with the ordinary
pullIso carries the ordinary square to the degree-zero derived square; its
comparison is the literal fieldCompScalarPull, identified by taking mates.
Finally commute that square with the shift by 2e, using the specified derived
adjunction shift comparisons. Invert the first line-pullback isomorphism and
postcompose with p'.derived to obtain the displayed equation. No multiplication
of two Tate degrees or smooth trace is involved. -/
theorem fieldCompositionSourceLinePullback
    (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (hunit : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    [∀ T : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (Λ := c.obj ell) (Λ' := c'.obj ell) a.hom.hom T))]
    {X Y : Scheme.{u}} [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)]
    (f : X ⟶ Y) (p : LinePullCoordinates ell c f)
    (p' : LinePullCoordinates ell c' f)
    (Px : ScalarLineCoordinates ell a hunit X)
    (Py : ScalarLineCoordinates ell a hunit Y) (e : ℕ) :
    (scalarSixChange a X).map (p.derived ell e).inv ≫
        (fieldCompScalarPull ell a f).hom.app (c.derivedLine ell Y e) ≫
        (actualPull (c'.obj ell) f).map (scalarLineMap ell a Y e (Py.power e)) ≫
        (p'.derived ell e).hom = scalarLineMap ell a X e (Px.power e) := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
