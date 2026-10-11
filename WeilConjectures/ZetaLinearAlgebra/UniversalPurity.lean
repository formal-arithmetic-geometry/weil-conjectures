/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ZetaLinearAlgebra.WeilFactorization

/-!
# Universal purity of an integral trace datum

Let `D` be a trace datum of length `2 * d` over an algebraically closed field `K` of
characteristic zero whose counting series has integer coefficients, and assume that for *every*
field embedding `ι : K → ℂ` the complexified reciprocal characteristic polynomial `ι (D.P i)` is
pure of weight `i`. Then `ι (D.P i)` is *universally* pure of weight `i`: every complex root `z`
is algebraic over `ℚ`, and every conjugate of `z` over `ℚ` has the same absolute value.

Algebraicity comes from the integral presentation `Z = A / B` of the counting series: the
weights separate the odd and even parity products of the `D.P i`, which are therefore the images
of `A` and `B` (`Polynomial.isAlgebraic_of_mem_roots_of_prod_mul_eq`). For the conjugates, a
root `z = ι β` with `β ∈ K` algebraic over `ℚ` and a conjugate `y` of `z` give a second
embedding `ι'` of `K` with `ι' β = y`, provided every embedding of `ℚ(β)` into `ℂ` extends to
`K`; purity for `ι'` bounds `y`. For `K = ℚ̄_ℓ` the extension property is the blueprint lemma
`lem-embedding-extension`.

## Main statements

- `TraceDatum.isUniversallyPureOfWeight_map_P`: universal purity of an integral trace datum which
  is pure for every embedding.
-/

@[expose] public section

universe u v

namespace TraceDatum

variable {K : Type u} [Field K] [CharZero K] {q d : ℕ} (D : TraceDatum.{u, v} K (2 * d))

/-- **Universal purity of an integral trace datum** (the intrinsic-weight step of the blueprint
proof of `thm-weil-realization-independence`): if every embedding of a number field `ℚ(β) ⊆ K`
into `ℂ` extends to `K`, the counting series of `D` has integer coefficients, and `ι (D.P i)` is
pure of weight `i` for every embedding `ι : K → ℂ`, then `ι (D.P i)` is universally pure of
weight `i`. -/
theorem isUniversallyPureOfWeight_map_P [IsAlgClosed K] (hq : 1 < q)
    (hext : ∀ (β : K) (z : ℂ), IsIntegral ℚ β →
      Polynomial.aeval z (minpoly ℚ β) = 0 → ∃ ι : K →+* ℂ, ι β = z)
    (hpure : ∀ (ι : K →+* ℂ) (i : Fin (2 * d + 1)), ((D.P i).map ι).IsPureOfWeight q i.1)
    {Z : PowerSeries ℚ} (hZ : PowerSeries.map (algebraMap ℚ K) Z = D.zeta)
    (hint : ∃ Z' : PowerSeries ℤ, PowerSeries.map (Int.castRingHom ℚ) Z' = Z)
    (ι : K →+* ℂ) (i : Fin (2 * d + 1)) :
    ((D.P i).map ι).IsUniversallyPureOfWeight q i.1 :=
  sorry

end TraceDatum
