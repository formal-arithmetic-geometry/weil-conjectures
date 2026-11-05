/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.TraceSeries

/-!
# The alternating trace series of the cohomology of a variety

Let `X₀` be a scheme of finite type over the finite field `k₀`, `X = X₀ ⊗ k̄`, and `d ≥ 0`. In
every degree `i` the cohomology `Hⁱ(X, ℚ̄_ℓ)` of the constant Weil sheaf, with its global
geometric Frobenius `F`, is a Frobenius module
(`AlgebraicGeometry.WeilSheaf.cohomology`). The *alternating trace series* of the finite graded
family `(Hⁱ(X, ℚ̄_ℓ), F)_{0 ≤ i ≤ 2d}` is

`str_F(T) = ∑_{n ≥ 1} (∑_{i = 0}^{2d} (-1) ^ i tr (F ^ n ∣ Hⁱ(X, ℚ̄_ℓ))) T ^ n / n`.

In the blueprint `X₀` is smooth, proper and geometrically connected of pure dimension `d`, so
that `I = {0, …, 2d}` contains every degree with nonzero cohomology; the definition itself needs
no such hypothesis.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.adicConstantAlternatingTraceSeries`: the alternating trace
  series `str_F(T)` of the cohomology of `X` in degrees `0, …, 2d`.
- `AlgebraicGeometry.WeilSheaf.coeff_adicConstantAlternatingTraceSeries`: its coefficients
  `(∑_{i = 0}^{2d} (-1) ^ i tr (F ^ n ∣ Hⁱ(X, ℚ̄_ℓ))) / n`.
-/

@[expose] public section

universe u

open PowerSeries

namespace AlgebraicGeometry.WeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

end AlgebraicGeometry.WeilSheaf
