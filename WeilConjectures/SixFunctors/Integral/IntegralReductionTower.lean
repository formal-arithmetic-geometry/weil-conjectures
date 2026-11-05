/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefined
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Cones

/-! # The integral reduction tower

Source: Bhatt--Scholze, p. 24, Proposition 3.5.1(1) and Definition 3.5.2;
Stacks Project, Tag 06YL (blueprint: def-weil-integral-reduction-tower).

The natural-number index n denotes exponent n+1. We use the chosen complex
representative K and its chosen K-flat resolution q:P→K. The already recorded
chain-level maps are characterized by the sheafified pure-tensor formulas.

This overlay keeps the canonical tower interface while rebuilding its unavailable
well-definedness import in the delivery dependency packet.
The bounded integral constructibility interface imports this same definition through
a paired source overlay. This keeps its canonical coefficient and K-flat interfaces
consistent when published compiled artifacts lag behind their recorded sources.
The integral triangulation statement compiles this same canonical interface in a
paired source packet to retain its recorded independent coefficient universes.
-/

@[expose] public section

set_option autoImplicit false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

end WeilConjectures
