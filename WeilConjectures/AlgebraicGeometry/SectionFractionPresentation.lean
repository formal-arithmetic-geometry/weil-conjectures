/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Quotient.Defs

/-! # Fractions of tensor-power sections

Source: Stacks Project, Properties, Section 0B5K, equation module-invert-s (Tag 0B5L)
(blueprint: def-sc-section-fraction-presentation).

This is the generators-and-relations presentation of the degree-zero localization:
`[n,t]` represents `t/s^n`, and `[n,t] = [n+b,t ⊗ s^b]`.
Only nonnegative twists occur in degree-zero fractions, even when the numerator module
is graded by all integers. Addition and scalar multiplication are the quotient operations.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
