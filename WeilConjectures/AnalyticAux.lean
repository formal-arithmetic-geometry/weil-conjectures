/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecificLimits.Normed
public import WeilConjectures.EulerProductAux

@[expose] public section

/-!
# Analytic evaluation of products of geometric series

This file proves the analytic counterpart of the formal Euler product computations of
`WeilConjectures.EulerProductAux`: for a family of exponents `d : ι → ℕ` with
`d i ≠ 0` such that `{i | d i ≤ n}` is finite for every `n`, and a complex number `z`
with `‖z‖ < 1` such that `∑ ‖z‖ ^ d i` converges, the infinite product
`∏ (1 - z ^ d i)⁻¹` converges in `ℂ` and equals the evaluation at `z` of the formal
infinite product `∏ (1 - X ^ d i)⁻¹ ∈ ℚ⟦X⟧`, i.e. the convergent power series
`∑ cₙ zⁿ` where `cₙ` are the coefficients of the formal product.

The proof proceeds by exact finite-level identities (finite products of geometric series
evaluate via Cauchy products, matching `PowerSeries.coeff_mul` termwise), together with
nonnegativity and monotonicity of the coefficients in the index set, an exponential
bound for the dominating series, and dominated convergence along the net of finite
subsets.
-/

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

namespace PowerSeries

variable {ι : Type*} {d : ι → ℕ} {z : ℂ}

end PowerSeries
