/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Data.ZMod.Basic

/-! # A non-finite kernel of a scalar endomorphism
Source: the non-coherent-ring example in the proof of
`det-def-sfb-bounded-constructible`. The square-zero extension gives a shorter model.
(blueprint: lem-sfb-nonfinite-multiplication-kernel)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

namespace BoundedConstructibleCounterexample

/-- The countably generated square-zero ideal.
Source: blueprint non-coherent-ring example.
(blueprint: lem-sfb-nonfinite-multiplication-kernel) -/
abbrev IdealSpace := ℕ →₀ Scalar.{u}

/-- The square-zero coefficient ring.
Source: blueprint non-coherent-ring example.
(blueprint: lem-sfb-nonfinite-multiplication-kernel) -/
abbrev Coeff := TrivSqZeroExt Scalar.{u} IdealSpace.{u}

end BoundedConstructibleCounterexample
