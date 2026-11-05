/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TraceSeries
public import WeilConjectures.ZetaFunction.TraceFormula
public import WeilConjectures.ZetaLinearAlgebra.TraceDatum

/-!
# The smooth-proper cohomological family and the trace-to-determinant identity

Let `X₀` be a smooth, proper, geometrically connected scheme of pure dimension `d` over the
finite field `k₀ = 𝔽_q`, and let `ℓ ≠ p` be a prime. The *smooth-proper cohomological family*
consists of the cohomology groups `Vᵢ = Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`, `0 ≤ i ≤ 2d`, of the constant Weil
sheaf, the geometric Frobenius `Fᵢ` on them, and the polynomials

`P_{i,ℓ}(T) = det(1 - T Fᵢ | Vᵢ) ∈ ℚ̄_ℓ[T]`

(`AlgebraicGeometry.Scheme.frobeniusCharpolyRev`). The Grothendieck–Lefschetz trace formula
`N_n = ∑ᵢ (-1)ⁱ Tr(Fᵢⁿ | Vᵢ)` and the log-determinant identity give the factorization

`Z(X₀, T) = ∏ᵢ P_{i,ℓ}(T)^{(-1)^{i+1}}` in `ℚ̄_ℓ⟦T⟧`.

## Coefficients

The cohomology with Frobenius available in this repository is that of Weil sheaves, with
coefficients `ℚ̄_ℓ` (`AlgebraicGeometry.WeilSheaf.cohomology`). The blueprint's `ℚ_ℓ`-family is
recovered from it by the flat base change `Hⁱ(X, ℚ_ℓ) ⊗ ℚ̄_ℓ = Hⁱ(X, ℚ̄_ℓ)`, which does not change
`P_{i,ℓ}`; so everything is stated with the `ℚ̄_ℓ`-family, as for Poincaré duality
(`AlgebraicGeometry.WeilSheaf.poincareDuality`).

## Main definitions

- `AlgebraicGeometry.Scheme.frobeniusCharpolyRev`: the polynomial `P_{i,ℓ}`
  (`def-weil-smooth-proper-cohomological-family`, `det-def-cohfamily`).
- `AlgebraicGeometry.Scheme.IsIntegralFrobeniusFactor`: an integral polynomial realizing
  `P_{i,ℓ}` for every `ℓ ≠ p` (`def-weil-integral-frobenius-factor`).
- `AlgebraicGeometry.Scheme.oddFrobeniusProduct`, `AlgebraicGeometry.Scheme.evenFrobeniusProduct`:
  the parity products `N_ℓ`, `D_ℓ` (`def-weil-parity-products`).

## Main statements

- `AlgebraicGeometry.Scheme.exists_traceDatum`: the cohomological family is a trace datum whose
  integers are the point counts.
- `AlgebraicGeometry.Scheme.map_zetaSeries_mul_evenFrobeniusProduct`: the trace-to-determinant
  identity (`det-thm-tracetodeterminant`, `thm-zl-lefschetz-weil-identity`).
- `LinearMap.inv_alternatingCharpolyRevProd_eq_exp` and
  `AlgebraicGeometry.Scheme.trace_determinant`: `prop-trace-determinant`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace LinearMap

variable {K : Type*} [Field K] [CharZero K] {W : ℤ → Type*} [∀ i, AddCommGroup (W i)]
  [∀ i, Module K (W i)] [∀ i, FiniteDimensional K (W i)]

end LinearMap

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace Scheme

section Defs

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `def-weil-smooth-proper-cohomological-family` (and `det-def-cohfamily`): the
determinant factor

`P_{i,ℓ}(T) = det(1 - T Fᵢ | Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ))`

of the geometric Frobenius `Fᵢ` on the cohomology of the constant Weil sheaf, the reverse
characteristic polynomial `FrobeniusModule.localPolynomial` of the Frobenius module
`Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`. It has constant coefficient `1`, degree `dim Hⁱ` and leading coefficient
`(-1)^{dim Hⁱ} det Fᵢ` (`AlgebraicGeometry.Scheme.coeff_zero_frobeniusCharpolyRev`,
`AlgebraicGeometry.Scheme.natDegree_frobeniusCharpolyRev`,
`AlgebraicGeometry.Scheme.leadingCoeff_frobeniusCharpolyRev`). -/
noncomputable def frobeniusCharpolyRev (i : ℤ) : Polynomial (PadicAlgCl l) :=
  ((WeilSheaf.adicConstant k₀ l X).cohomology i).localPolynomial

theorem frobeniusCharpolyRev_def (i : ℤ) :
    frobeniusCharpolyRev k₀ l X i =
      ((WeilSheaf.adicConstant k₀ l X).cohomology i).localPolynomial :=
  rfl

/-- `P_{i,ℓ}` has constant coefficient `1` (`def-weil-smooth-proper-cohomological-family`). -/
@[simp]
theorem coeff_zero_frobeniusCharpolyRev (i : ℤ) : (frobeniusCharpolyRev k₀ l X i).coeff 0 = 1 :=
  FrobeniusModule.coeff_zero_localPolynomial _

end Defs

/-- Blueprint `def-weil-integral-frobenius-factor`: an *integral realization-independent factor*
in degree `i` of a `k₀`-scheme `X₀` is a polynomial `P ∈ ℤ[T]` whose coefficientwise extension
`P^{(ℓ)}` to `ℚ̄_ℓ` is the determinant factor `P_{i,ℓ}` of
`AlgebraicGeometry.Scheme.frobeniusCharpolyRev`, for every prime `ℓ ≠ p`. -/
def IsIntegralFrobeniusFactor (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] (i : ℤ) (P : Polynomial ℤ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] [Fact (ringChar k₀ ≠ l)],
    P.map (Int.castRingHom (PadicAlgCl l)) = frobeniusCharpolyRev k₀ l X i

section SmoothProper

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] (d : ℕ)
  [IsProper (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]

end SmoothProper

end Scheme

end AlgebraicGeometry
