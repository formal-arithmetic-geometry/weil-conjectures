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
  (`def-weil-smooth-proper-cohomological-family`, `sk-def-cohfamily`).
- `AlgebraicGeometry.Scheme.IsIntegralFrobeniusFactor`: an integral polynomial realizing
  `P_{i,ℓ}` for every `ℓ ≠ p` (`def-weil-integral-frobenius-factor`).
- `AlgebraicGeometry.Scheme.oddFrobeniusProduct`, `AlgebraicGeometry.Scheme.evenFrobeniusProduct`:
  the parity products `N_ℓ`, `D_ℓ` (`def-weil-parity-products`).

## Main statements

- `AlgebraicGeometry.Scheme.exists_traceDatum`: the cohomological family is a trace datum whose
  integers are the point counts.
- `AlgebraicGeometry.Scheme.map_zetaSeries_mul_prod_even_eq_prod_odd`: the trace-to-determinant
  identity (`sk-thm-tracetodeterminant`, `thm-zl-lefschetz-weil-identity`).
- `LinearMap.exp_traceSeries_mul_charpolyRev` and
  `AlgebraicGeometry.Scheme.traceDeterminant`: `prop-trace-determinant`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace Scheme

section Defs

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `def-weil-smooth-proper-cohomological-family` (and `sk-def-cohfamily`): the
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

/-- `P_{i,ℓ}` has degree `dim Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)` (`def-weil-smooth-proper-cohomological-family`). -/
theorem natDegree_frobeniusCharpolyRev (i : ℤ) :
    (frobeniusCharpolyRev k₀ l X i).natDegree =
      Module.finrank (PadicAlgCl l) ((WeilSheaf.adicConstant k₀ l X).cohomology i).carrier :=
  FrobeniusModule.natDegree_localPolynomial _

/-- `P_{i,ℓ}` has leading coefficient `(-1)^{dim Hⁱ} det Fᵢ`
(`def-weil-smooth-proper-cohomological-family`). -/
theorem leadingCoeff_frobeniusCharpolyRev (i : ℤ) :
    (frobeniusCharpolyRev k₀ l X i).leadingCoeff =
      (-1) ^ Module.finrank (PadicAlgCl l)
        ((WeilSheaf.adicConstant k₀ l X).cohomology i).carrier *
        LinearMap.det ((WeilSheaf.adicConstant k₀ l X).cohomology i).frobeniusEnd :=
  FrobeniusModule.leadingCoeff_localPolynomial _

/-- Blueprint `def-weil-parity-products`: the odd parity product
`N_ℓ(T) = ∏_{0 ≤ i ≤ 2d, i odd} P_{i,ℓ}(T)`. -/
noncomputable def oddFrobeniusProduct (d : ℕ) : Polynomial (PadicAlgCl l) :=
  ∏ i ∈ (Finset.range (2 * d + 1)).filter Odd, frobeniusCharpolyRev k₀ l X i

/-- Blueprint `def-weil-parity-products`: the even parity product
`D_ℓ(T) = ∏_{0 ≤ i ≤ 2d, i even} P_{i,ℓ}(T)`. -/
noncomputable def evenFrobeniusProduct (d : ℕ) : Polynomial (PadicAlgCl l) :=
  ∏ i ∈ (Finset.range (2 * d + 1)).filter Even, frobeniusCharpolyRev k₀ l X i

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

/-- The smooth-proper cohomological family is a trace datum: the cohomology groups
`Hⁱ(X₀ ⊗ k̄, ℚ̄_ℓ)`, `0 ≤ i ≤ 2d`, with the geometric Frobenius, and the point counts
`N_n = #X₀(𝔽_{qⁿ})`, related by the Grothendieck–Lefschetz trace formula
(`AlgebraicGeometry.WeilSheaf.pointCount_eq_sum_trace_cohomology`). The spaces and the
endomorphisms are the cohomology groups and their Frobenius, on the nose. -/
theorem exists_traceDatum :
    ∃ D : TraceDatum.{0, u + 1} (PadicAlgCl l) (2 * d),
      (∀ i, D.V i = ((WeilSheaf.adicConstant k₀ l X).cohomology (i : ℕ)).carrier) ∧
      (∀ i, D.P i = frobeniusCharpolyRev k₀ l X (i : ℕ)) ∧
      ∀ n, D.N n = (X ↘ Spec (CommRingCat.of k₀)).pointCount n :=
  sorry

/-- Blueprint `sk-thm-tracetodeterminant` and `thm-zl-lefschetz-weil-identity`
(trace-to-determinant identity): for `X₀` smooth and proper of pure dimension `d`,

`Z(X₀, T) = ∏_{i = 0}^{2d} P_{i,ℓ}(T)^{(-1)^{i+1}}` in `ℚ̄_ℓ⟦T⟧`,

stated with the denominators cleared:
`Z(X₀, T) · ∏_{i even} P_{i,ℓ}(T) = ∏_{i odd} P_{i,ℓ}(T)`. The right hand side is a quotient of
polynomials with constant coefficient `1`, so the identity holds in `ℚ̄_ℓ(T) ∩ ℚ̄_ℓ⟦T⟧`. -/
theorem map_zetaSeries_mul_evenFrobeniusProduct :
    PowerSeries.map (algebraMap ℚ (PadicAlgCl l)) (X ↘ Spec (CommRingCat.of k₀)).zetaSeries *
        (evenFrobeniusProduct k₀ l X d : PowerSeries (PadicAlgCl l)) =
      (oddFrobeniusProduct k₀ l X d : PowerSeries (PadicAlgCl l)) :=
  sorry

end SmoothProper

end Scheme

end AlgebraicGeometry
