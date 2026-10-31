/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quadratic formal curve and coefficient algebra

Source: Stacks Project, curves.tex, Tag 0C4A (lemma-2-branches-delta-1),
Cases I and II, interchanging X and Y in Case II; Tag 0CBT(1).
(blueprint: def-sfb-quadratic-formal-curve)

These are the explicit polynomial, formal equation, two quotient algebras and
coordinate classes used in the quadratic normalization and coefficient charts.
No nondegeneracy is required to form the objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace QuadraticSeries

/-- The polynomial aZ² + bZ + c of Stacks 0C4A, Case II with coordinates interchanged.
(blueprint: def-sfb-quadratic-formal-curve) -/
abbrev polynomial {F : Type u} [Field F] (a b c : F) : Polynomial F :=
  Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c

/-- The equation aX² + bXY + cY² of Stacks 0C4A, Cases I and II.
(blueprint: def-sfb-quadratic-formal-curve) -/
abbrev equation {F : Type u} [Field F] (a b c : F) : MvPowerSeries (Fin 2) F :=
  MvPowerSeries.C a * MvPowerSeries.X 0 ^ 2 +
    MvPowerSeries.C b * MvPowerSeries.X 0 * MvPowerSeries.X 1 +
    MvPowerSeries.C c * MvPowerSeries.X 1 ^ 2

/-- The completed quadratic curve ring R of Stacks 0C4A, Cases I and II.
(blueprint: def-sfb-quadratic-formal-curve) -/
abbrev CurveRing {F : Type u} [Field F] (a b c : F) :=
  MvPowerSeries (Fin 2) F ⧸ Ideal.span {equation a b c}

/-- The quadratic coefficient algebra L of Stacks 0C4A, unifying Cases I and II.
It can be a product; no domain structure is imposed.
(blueprint: def-sfb-quadratic-formal-curve) -/
abbrev CoefficientAlgebra {F : Type u} [Field F] (a b c : F) :=
  AdjoinRoot (polynomial a b c)

/-- The class x of the first coordinate in the curve ring, Stacks 0C4A.
(blueprint: def-sfb-quadratic-formal-curve) -/
abbrev x {F : Type u} [Field F] (a b c : F) : CurveRing a b c :=
  Ideal.Quotient.mk (Ideal.span {equation a b c}) (MvPowerSeries.X 0)

/-- The class y of the second coordinate in the curve ring, Stacks 0C4A.
(blueprint: def-sfb-quadratic-formal-curve) -/
abbrev y {F : Type u} [Field F] (a b c : F) : CurveRing a b c :=
  Ideal.Quotient.mk (Ideal.span {equation a b c}) (MvPowerSeries.X 1)

end QuadraticSeries
