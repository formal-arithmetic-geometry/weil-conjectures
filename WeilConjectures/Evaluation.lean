/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AnalyticAux
public import WeilConjectures.EulerProduct

@[expose] public section

/-!
# The zeta function is the evaluation of the zeta series

For a scheme `X` of finite type over a finite field `k` with `q` elements, given by a
structure morphism `f : X ⟶ Spec k`, we prove Serre's identity

`ζ_X(s) = Z(X, q ^ (-s))`,

where `ζ_X` is the zeta function of `X` as an abstract scheme
(`AlgebraicGeometry.Scheme.zeta`, an Euler product over the points with finite residue
field) and `Z(X, t)` is the zeta series of `X` over `k`
(`AlgebraicGeometry.Scheme.Hom.zetaSeries`), evaluated at `t = q ^ (-s)` as a convergent
power series.

The identity holds under the correct convergence assumptions: `‖q ^ (-s)‖ < 1` and
summability of `∑ ‖q ^ (-s)‖ ^ deg x` over the closed points of `X` (which is precisely
absolute convergence of the Euler product; by a theorem of Serre both hold whenever
`re s > dim X`, but we take them as hypotheses). Both assumptions are necessary: for `X`
finite and nonempty the power series diverges at `‖q ^ (-s)‖ ≥ 1` while the Euler
product is a finite product.

The proof combines the formal Euler product `Z(X, t) = ∏ (1 - t ^ deg x)⁻¹`
(`WeilConjectures.EulerProduct`) with its analytic counterpart
(`WeilConjectures.AnalyticAux`), and the identity `#κ(x) = q ^ deg x` for the
norms of closed points.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.pointNorm_eq_pow_degreeOver`: `#κ(x) = q ^ deg x`.
- `AlgebraicGeometry.Scheme.Hom.zeta_eq_tsum_coeff_zetaSeries`: `ζ_X(s) = Z(X, q^(-s))`.
- `AlgebraicGeometry.Scheme.Hom.multipliable_eulerFactor`: the Euler product defining
  `ζ_X` converges under the same assumptions.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- The norm of a point of a scheme over a finite field `k` with `q` elements is
`q ^ deg x`. -/
theorem Hom.pointNorm_eq_pow_degreeOver [Finite k] (f : X.Hom (Spec (.of k))) {x : X}
    (hx : x ∈ X.finitePoints) :
    X.pointNorm x = Nat.card k ^ f.degreeOver x := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have : Finite (X.residueField x) := X.mem_finitePoints.mp hx
  have : Module.Finite k (X.residueField x) := Module.Finite.of_finite
  unfold Scheme.pointNorm Hom.degreeOver
  exact Module.natCard_eq_pow_finrank

/-- The Euler factor of the zeta function at a point of degree `d` over `k` is the
geometric factor `(1 - (q ^ (-s)) ^ d)⁻¹`. -/
theorem Hom.eulerFactor_eq [Finite k] (f : X.Hom (Spec (.of k))) {x : X}
    (hx : x ∈ X.finitePoints) (s : ℂ) :
    X.eulerFactor x s = (1 - ((Nat.card k : ℂ) ^ (-s)) ^ f.degreeOver x)⁻¹ := by
  unfold Scheme.eulerFactor
  rw [f.pointNorm_eq_pow_degreeOver hx, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]


end AlgebraicGeometry.Scheme
