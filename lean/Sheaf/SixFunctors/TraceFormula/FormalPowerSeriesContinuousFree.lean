/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Sheaf.RingTheory.ContinuousKaehlerDifferential
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-! # Continuous differentials of a formal power-series ring

Source: Stacks Project, algebra.tex, Tags 00RU, 00RX, 02HQ and 032C; the explicit
finite-truncation and shifted-lift argument in the DAG
(blueprint: lem-trf-formal-power-series-continuous-free).

The differential module and derivation are the existing compatible-family constructions
`KaehlerDifferential.Continuous` and `KaehlerDifferential.continuousD`. Their positive
quotient exponents are indexed by `r + 1`; the omitted exponent-zero differential module
is zero and adds no compatibility condition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public section

open scoped BigOperators

universe u

namespace RingTheory

/-- Continuous differentials of `F[[t₁, …, tₙ]]` have the specified coordinate basis and
termwise derivative formula, in every characteristic and including no variables.

Source: Stacks Project, algebra.tex, Tags 00RX (polynomial Kähler basis), 00RU
(conormal sequence), 02HQ (differentials modulo ideal powers), and 032C (power-series
completeness); the continuous inverse-limit conclusion is the auxiliary argument in the
DAG, not the statement of Curves Tag 0C4D
(blueprint: lem-trf-formal-power-series-continuous-free).

Proof:
1. Put `P = F[t₁, …, tₙ]`, `J = (t₁, …, tₙ)` in `P`, and `m = (t₁, …, tₙ)`
   in `D = F[[t₁, …, tₙ]]`. By
   `lem-weil-pbc-power-series-combined-ideal-coefficients` with coefficient ideal zero,
   reduction modulo `m^r` is finite polynomial truncation in total degrees less than `r`.
   Its polynomial kernel is `J^r`, giving `P/J^r = D/m^r = Q_r`.
2. For `M = D^n`, let `theta_r(a) = sum_i (a_i mod m^r) d(t_i mod m^r)`.
   Apply `lem-weil-pbc-jacobi-zariski-differential-maps` and
   `lem-weil-pbc-polynomial-ring-kahler-basis` to `F → P → P/J^r`.
   They make `theta_r` surjective and identify its kernel `K_r` as `m^r M` plus
   the span of the gradient vectors of polynomials in `J^r`.
3. Termwise differentiation lowers total degree by at most one. The coefficient
   criterion therefore gives `m^r M ≤ K_r ≤ m^(r-1) M`. This uses no division,
   so the bounds hold in every characteristic.
4. The quotient-induced differential transitions send `d(b)` to `d(b mod m^r)`.
   Thus they carry `theta_(r+1)(a)` to `theta_r(a)`, defining a `D`-linear map
   `Phi : M → lim_r Omega_(Q_r/F)`.
5. For a compatible family `omega`, choose a lift `a_(r+1)` under `theta_(r+1)`.
   Its class `b_r` modulo `m^r M` is independent of the lift by the upper kernel
   bound, and the classes are compatible. By
   `lem-weil-pbc-power-series-variables-complete` and
   `def-weil-pbc-adically-complete-ring`, coordinatewise completeness gives a unique
   `a` with these reductions. This defines a linear map `Psi`.
6. Constant lifts give `Psi(Phi(a)) = a`. Conversely, `a - a_(r+1)` is in
   `m^r M ≤ K_r`, so `theta_r(a) = omega_r`, giving `Phi(Psi(omega)) = omega`.
   The image of the `i`-th coordinate vector is exactly the compatible family
   `continuousD(t_i)`, proving the specified basis assertion.
7. For a series `h`, truncate in total degrees less than `r+1` to a polynomial `p`.
   The coefficient criterion gives `h-p ∈ m^(r+1)` and
   `partial_i(h)-partial_i(p) ∈ m^r`. The polynomial derivative formula transported
   to `Q_r` therefore gives the required equality at level `r`. Equality of all
   components gives the displayed continuous derivative formula. -/
theorem formalPowerSeriesContinuousDifferentials_free
    (F : Type u) [Field F] (n : ℕ) :
    ∃ b : Module.Basis (Fin n) (MvPowerSeries (Fin n) F)
        (KaehlerDifferential.Continuous F (MvPowerSeries (Fin n) F)
          (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) F)))),
      (∀ i : Fin n, b i =
        KaehlerDifferential.continuousD F (MvPowerSeries (Fin n) F)
          (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) F)))
          (MvPowerSeries.X i)) ∧
      ∀ h : MvPowerSeries (Fin n) F,
        KaehlerDifferential.continuousD F (MvPowerSeries (Fin n) F)
            (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) F))) h =
          ∑ i : Fin n, (MvPowerSeries.pderiv F i h) • b i := by
  sorry

end RingTheory
