/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaFunction.BettiNumbers
public import WeilConjectures.ZetaLinearAlgebra.Pairing
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# Duality reciprocity of the Frobenius factors

Let `D` be a trace datum of length `2 * d` which is self-dual for the similitude factor `qᵈ`,
the linear algebra shadow of Poincaré duality used in
`WeilConjectures.ZetaLinearAlgebra.FunctionalEquation`. Writing `b i` for the dimension of
`D.V i` and `D i = det (D.F i)` for the determinant constant of degree `i`, duality gives

* the reciprocity of the factors themselves, which is
  `LinearMap.C_det_mul_charpolyRev_of_similitude` of
  `WeilConjectures.ZetaLinearAlgebra.Pairing`;
* the product rule `D i * D (2 * d - i) = q ^ (d * b i)`;
* the parity `d * χ` even, where `χ = ∑ᵢ (-1)ⁱ b i`.

The parity is what makes the constant `q ^ (d * χ / 2)` of the functional equation
`WeilConjectures.ZetaFunction.FunctionalEquation` an integer power of `q`. For odd `d` it
rests on the middle pairing being alternating, which forces `b d` to be even; that sign rule
is part of Poincaré duality and is taken here as the hypothesis `halt`.

## Main statements

- `TraceDatum.det_mul_det_rev_of_pairing`: the product rule for the determinant constants and
  the parity of `d * χ`.
-/

@[expose] public section

universe u v

open scoped Polynomial

namespace TraceDatum

variable {K : Type u} [Field K] [CharZero K] {q d : ℕ} (D : TraceDatum.{u, v} K (2 * d))
  {p : ∀ i : Fin (2 * d + 1), D.V i →ₗ[K] D.V i.rev →ₗ[K] K}

/-- Blueprint `sk-prop-reciprocity`: Duality reciprocity of the factors.

For a trace datum that is self-dual for the similitude factor `qᵈ`, the determinant constants
`D i = det (D.F i)` satisfy `D i * D (2 * d - i) = q ^ (d * b i)`, and `d * χ` is even. The
first displayed identity of the blueprint statement, expressing `D.P (2 * d - i)` through
`D.P i`, is `LinearMap.C_det_mul_charpolyRev_of_similitude`. The hypothesis `halt` records
that the middle pairing is alternating for odd `d`, so that the middle Betti number is
even. -/
theorem det_mul_det_rev_of_pairing (hq : 1 < q) (hp : ∀ i, (p i).IsPerfPair)
    (hFG : ∀ i, ∀ v w, p i (D.F i v) (D.F i.rev w) = (q : K) ^ d * p i v w)
    (halt : Odd d → Even (Module.finrank K (D.V ⟨d, by omega⟩))) :
    (∀ i : Fin (2 * d + 1), LinearMap.det (D.F i) * LinearMap.det (D.F i.rev) =
        (q : K) ^ (d * Module.finrank K (D.V i))) ∧
      Even ((d : ℤ) * AlgebraicGeometry.weilEulerChar D.P) :=
  sorry

end TraceDatum

end
