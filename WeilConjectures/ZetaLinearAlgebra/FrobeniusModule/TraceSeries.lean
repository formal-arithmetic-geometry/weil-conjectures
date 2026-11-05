/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.DetTrace
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule

/-!
# Trace series of Frobenius modules

Let `(V, F)` be a Frobenius module over a field `K`: a finite-dimensional `K`-vector space
with an automorphism `F`. Its *trace series* and its *determinant* are

`tr_F(T) = ∑_{n ≥ 1} tr (F ^ n ∣ V) T ^ n / n ∈ T K⟦T⟧`,  `P_{(V, F)}(T) = det (1 - T F ∣ V)`.

The determinant is `FrobeniusModule.localPolynomial`; it has constant coefficient `1` and
degree `dim V`, its leading coefficient `(-1) ^ dim V det F` being nonzero. For a finite graded
family `(V_i, F_i)_{i ∈ I}`, `I ⊆ ℤ` finite, the *alternating trace series* is

`str_F(T) = ∑_{n ≥ 1} (∑_{i ∈ I} (-1) ^ i tr (F_i ^ n ∣ V_i)) T ^ n / n
  = ∑_{i ∈ I} (-1) ^ i tr_{F_i}(T)`.

No semisimplicity of the Frobenius is assumed. In the geometric situation of the blueprint the
family is the cohomology `Hⁱ(X ⊗ k̄, ℚ̄_ℓ)` of the constant Weil sheaf on a smooth proper
`k₀`-scheme `X` of pure dimension `d`, with its global geometric Frobenius
(`AlgebraicGeometry.WeilSheaf.cohomology (AlgebraicGeometry.WeilSheaf.adicConstant k₀ l X)`), and
`I = {0, …, 2d}`, i.e. `s = Finset.Icc 0 (2 * d)`.

## Main declarations

- `FrobeniusModule.traceSeries`: the trace series of a Frobenius module.
- `FrobeniusModule.alternatingTraceSeries`: the alternating trace series of a finite graded
  family of Frobenius modules.
- `FrobeniusModule.coeff_alternatingTraceSeries`: its coefficients
  `(∑_i (-1) ^ i tr (F_i ^ n)) / n`.
- `FrobeniusModule.coeff_zero_localPolynomial`, `FrobeniusModule.natDegree_localPolynomial` and
  `FrobeniusModule.leadingCoeff_localPolynomial`: `det (1 - T F)` has constant coefficient `1`,
  degree `dim V` and leading coefficient `(-1) ^ dim V det F ≠ 0`.
-/

@[expose] public section

universe u v

open PowerSeries

namespace FrobeniusModule

variable {K : Type v} [Field K]

/-- The determinant `det (1 - T F ∣ V)` of a Frobenius module has constant coefficient `1`
(blueprint: `def-zl-frobenius-trace-series`). -/
@[simp]
theorem coeff_zero_localPolynomial (M : FrobeniusModule.{u, v} K) :
    M.localPolynomial.coeff 0 = 1 :=
  LinearMap.coeff_zero_charpolyRev _

/-- The determinant `det (1 - T F ∣ V)` of a Frobenius module has degree `dim V`, since its
Frobenius is invertible (blueprint: `def-zl-frobenius-trace-series`). -/
theorem natDegree_localPolynomial (M : FrobeniusModule.{u, v} K) :
    M.localPolynomial.natDegree = Module.finrank K M.carrier :=
  LinearMap.natDegree_charpolyRev (LinearEquiv.isUnit_det' M.frobenius)

end FrobeniusModule
