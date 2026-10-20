/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.AlgebraicallyClosedCoefficients
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Standard pairs on constructible coefficient categories

Source: Weil conjectures blueprint, `sec-smooth-base-change/sk-rem-rest`,
`prop-weil-localized-tstructure` and `prop-weil-pbc-integral-tstructure`
(blueprint: def-weil-constructible-standard-tstructure).

Integral classes use the cohomology of completed-coefficient module sheaves.
Rational and algebraically closed classes are the indicated isomorphism closures.
The shifted classes use cohomological shifts. No t-structure axioms are asserted.
-/

@[expose] public section

set_option autoImplicit false

universe d u v

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Y : AlgebraicGeometry.Scheme.{u})

/-- Integral nonpositive objects: cohomology vanishes in every positive degree.
Source: blueprint `prop-weil-pbc-integral-tstructure`, first display
(blueprint: def-weil-constructible-standard-tstructure). -/
def integralConstructibleLEZero :
    ObjectProperty (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
  fun K ↦ ∀ r : ℤ, 0 < r →
    IsZero ((@DerivedCategory.homologyFunctor (completedIntegralModuleSheaves l E Y D hl)
      _ _ (HasDerivedCategory.standard _) r).obj K.obj)

/-- Integral nonnegative objects: cohomology vanishes in every negative degree.
Source: blueprint `prop-weil-pbc-integral-tstructure`, second display
(blueprint: def-weil-constructible-standard-tstructure). -/
def integralConstructibleGEZero :
    ObjectProperty (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
  fun K ↦ ∀ r : ℤ, r < 0 →
    IsZero ((@DerivedCategory.homologyFunctor (completedIntegralModuleSheaves l E Y D hl)
      _ _ (HasDerivedCategory.standard _) r).obj K.obj)

/-- Rational nonpositive objects are rationally isomorphic to integral nonpositive ones.
Source: blueprint `prop-weil-localized-tstructure`, first display
(blueprint: def-weil-constructible-standard-tstructure). -/
def rationalConstructibleLEZero : ObjectProperty (rationalConstructibleCategory D l hl E Y) :=
  fun K ↦ ∃ L : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y,
    integralConstructibleLEZero D l hl E Y L ∧
      Nonempty (K ≅ (rationalConstructibleLocalization D l hl E Y).obj L)

/-- Rational nonnegative objects are rationally isomorphic to integral nonnegative ones.
Source: blueprint `prop-weil-localized-tstructure`, second display
(blueprint: def-weil-constructible-standard-tstructure). -/
def rationalConstructibleGEZero : ObjectProperty (rationalConstructibleCategory D l hl E Y) :=
  fun K ↦ ∃ L : boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y,
    integralConstructibleGEZero D l hl E Y L ∧
      Nonempty (K ≅ (rationalConstructibleLocalization D l hl E Y).obj L)

/-- The integral standard pair; its t-structure axioms are a separate assertion.
Source: blueprint `prop-weil-pbc-integral-tstructure`
(blueprint: def-weil-constructible-standard-tstructure). -/
def integralConstructibleStandardPair :=
  (integralConstructibleLEZero D l hl E Y, integralConstructibleGEZero D l hl E Y)

/-- The rational standard pair; no idempotent completion is taken.
Source: blueprint `prop-weil-localized-tstructure`
(blueprint: def-weil-constructible-standard-tstructure). -/
def rationalConstructibleStandardPair :=
  (rationalConstructibleLEZero D l hl E Y, rationalConstructibleGEZero D l hl E Y)

/-- Integral degree-n nonpositive objects are those whose n-shift is nonpositive.
Source: blueprint `def-weil-constructible-heart`, shifted standard classes
(blueprint: def-weil-constructible-standard-tstructure). -/
def integralConstructibleLE (n : ℤ) :
    ObjectProperty (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
  fun K ↦ integralConstructibleLEZero D l hl E Y
    ((shiftFunctor (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) n).obj K)

/-- Integral degree-n nonnegative objects are those whose n-shift is nonnegative.
Source: blueprint `def-weil-constructible-heart`, shifted standard classes
(blueprint: def-weil-constructible-standard-tstructure). -/
def integralConstructibleGE (n : ℤ) :
    ObjectProperty (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) :=
  fun K ↦ integralConstructibleGEZero D l hl E Y
    ((shiftFunctor (boundedConstructibleDerivedCompleteIntegralCategory D l hl E Y) n).obj K)

/-- Rational degree-n nonpositive objects, with the induced cohomological shift.
Source: blueprint `def-weil-constructible-heart`, shifted standard classes
(blueprint: def-weil-constructible-standard-tstructure). -/
def rationalConstructibleLE (n : ℤ) : ObjectProperty (rationalConstructibleCategory D l hl E Y) :=
  fun K ↦ rationalConstructibleLEZero D l hl E Y
    ((shiftFunctor (rationalConstructibleCategory D l hl E Y) n).obj K)

/-- Rational degree-n nonnegative objects, with the induced cohomological shift.
Source: blueprint `def-weil-constructible-heart`, shifted standard classes
(blueprint: def-weil-constructible-standard-tstructure). -/
def rationalConstructibleGE (n : ℤ) : ObjectProperty (rationalConstructibleCategory D l hl E Y) :=
  fun K ↦ rationalConstructibleGEZero D l hl E Y
    ((shiftFunctor (rationalConstructibleCategory D l hl E Y) n).obj K)

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Algebraically closed nonpositive objects are isomorphic to a nonpositive finite stage.
The finite field is transported by the recorded coefficient algebra equivalence.
Source: blueprint `def-weil-constructible-heart`, common-stage standard classes
(blueprint: def-weil-constructible-standard-tstructure). -/
def algebraicallyClosedConstructibleLEZero :
    ObjectProperty (algebraicallyClosedConstructibleCategory D l hl Ω Y) :=
  fun X ↦ ∃ (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : AlgebraicallyClosedCoefficients.Stage D l hl Ω Y L),
    rationalConstructibleLEZero D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y M ∧
      Nonempty (X ≅ (AlgebraicallyClosedCoefficients.inclusion L).obj M)

/-- Algebraically closed nonnegative objects are isomorphic to a nonnegative finite stage.
Source: blueprint `def-weil-constructible-heart`, common-stage standard classes
(blueprint: def-weil-constructible-standard-tstructure). -/
def algebraicallyClosedConstructibleGEZero :
    ObjectProperty (algebraicallyClosedConstructibleCategory D l hl Ω Y) :=
  fun X ↦ ∃ (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : AlgebraicallyClosedCoefficients.Stage D l hl Ω Y L),
    rationalConstructibleGEZero D l hl
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y M ∧
      Nonempty (X ≅ (AlgebraicallyClosedCoefficients.inclusion L).obj M)

/-- The algebraically closed standard pair on the common-stage category.
Source: blueprint `def-weil-constructible-heart`
(blueprint: def-weil-constructible-standard-tstructure). -/
def algebraicallyClosedConstructibleStandardPair :=
  (algebraicallyClosedConstructibleLEZero D l hl Y Ω,
    algebraicallyClosedConstructibleGEZero D l hl Y Ω)

/-- Algebraically closed degree-n nonpositive objects use the common-stage n-shift.
Source: blueprint `def-weil-constructible-heart`, shifted standard classes
(blueprint: def-weil-constructible-standard-tstructure). -/
def algebraicallyClosedConstructibleLE (n : ℤ) :
    ObjectProperty (algebraicallyClosedConstructibleCategory D l hl Ω Y) :=
  fun K ↦ algebraicallyClosedConstructibleLEZero D l hl Y Ω
    ((shiftFunctor (algebraicallyClosedConstructibleCategory D l hl Ω Y) n).obj K)

/-- Algebraically closed degree-n nonnegative objects use the common-stage n-shift.
Source: blueprint `def-weil-constructible-heart`, shifted standard classes
(blueprint: def-weil-constructible-standard-tstructure). -/
def algebraicallyClosedConstructibleGE (n : ℤ) :
    ObjectProperty (algebraicallyClosedConstructibleCategory D l hl Ω Y) :=
  fun K ↦ algebraicallyClosedConstructibleGEZero D l hl Y Ω
    ((shiftFunctor (algebraicallyClosedConstructibleCategory D l hl Ω Y) n).obj K)

end WeilConjectures
