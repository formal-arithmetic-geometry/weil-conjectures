/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.Paper.PurityRelativeKummerMaps

/-! # A component of the relative Kummer calculation

Source: blueprint sk-prop-a1-kummer, prop-pur-gm-relative-kummer.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry


namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] ProEtale.upperStar ProEtale.lowerStar
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ProEtale.derivedUpperStarLowerStarAdjunction ProEtale.derivedBaseChangeMap
  constantPullback twistPullback derivedCoefficientPullback relativeUnit kummerGenerator
  constant twist constantEtale twistEtale coordinateKummer coordinateClass



/-- Naturality of the coordinate boundary and invertibility of punctured-line exchange,
once the relative line and punctured-line calculations on both bases are known.
Source: blueprint prop-pur-gm-relative-kummer, proof steps 3 and 10--16
(blueprint: lem-pur-relative-kummer-exchange).

Proof: Pullback of the Kummer short exact sequence is a morphism to the Kummer
sequence on the new base. Naturality of connecting maps and coefficient insertion
therefore sends the boundary of t to that of its pullback t'. This gives the first
equality, including the standard single-complex and shift identifications. Exchange
is the canonical adjunction mate. Its composite with pullback of the unit is the
unit on the new base, by the triangle identity, so its degree-zero map preserves
constants. On an injective resolution the higher-image exchange restricts a cocycle
to the base-changed etale object. Its degree-one map thus carries the Kummer edge
section to that of t'. The given relative calculations make these maps isomorphisms
in degrees zero and one. Exact pullback commutes with cohomology; all remaining
positive degrees vanish by the given calculations, and negative degrees vanish by
left exactness of direct image. Cohomological detection gives derived invertibility.
Finally the exact site-comparison and its canonical counit mate identify this exchange with the
specified pro-etale exchange. The argument works for every map of k-schemes. -/
theorem relative_kummer_exchange (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {Y' Y : Scheme.{u}} (g : Y' ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (hY : P.RelativeKummerConclusions h Y a)
    (hY' : P.RelativeKummerConclusions h Y' (g ≫ a)) :
  P.CoordinateKummerNaturality h g a ∧
  IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} P.Coefficient)
    (puncturedSquare g)).app (P.derivedSheaf h (Punctured Y) true)) := by sorry

end WeilConjectures.PurityFiniteSetting
