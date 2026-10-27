/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Formal exponential of a bivariate series over a rational algebra

Source: the defining coefficient formula in the agent-stated class-two identity,
motivated by Milne, Algebraic Groups, §23h, equation (153), printed p.510
(blueprint: def-sfb-bivariate-formal-exponential).
-/

@[expose] public section

universe u

namespace MvPowerSeries

/-- The formal exponential on bivariate series with zero constant coefficient, defined
by its finite coefficient formula. The variables indexed by `Fin 2` are central and
commute, but the coefficient algebra need not be commutative. At multi-degree `d`,
only powers through `Finsupp.degree d` contribute when the input has zero constant
coefficient. This formula also specifies an extension to other inputs; only inputs
with zero constant coefficient are interpreted as formal exponentials.

Source: the defining formula preceding the agent-stated class-two identity; Milne,
Algebraic Groups, §23h, equation (153), printed p.510, motivation only
(blueprint: def-sfb-bivariate-formal-exponential). -/
noncomputable def bivariateExp {A : Type u} [Ring A] [Algebra ℚ A]
    (Z : MvPowerSeries (Fin 2) A) : MvPowerSeries (Fin 2) A :=
  fun d => ∑ n ∈ Finset.range (Finsupp.degree d + 1),
    ((n.factorial : ℚ)⁻¹) • coeff d (Z ^ n)

end MvPowerSeries
