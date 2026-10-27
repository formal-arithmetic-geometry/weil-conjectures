module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Sheaf.Analysis.Complex.CauchyGreenAnnulusFormula
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # Cauchy–Green reproduction of compactly supported test functions

Source: Demailly, Complex Analytic and Differential Geometry, I §3.A, formula (3.2)
and Corollary (3.4), printed p.21 (blueprint: lem-sfb-cauchy-green-test-function).

The kernel is written directly as `1 / ((Real.pi : ℂ) * w)`; division by zero gives
its prescribed value zero at the origin. The real differential in directions `1`
and `I` gives the two coordinate partial derivatives. The last clause allows any
replacement of the integrand's value at its pole.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace Complex

/-- The locally integrable Cauchy kernel reproduces real-smooth compactly supported
functions from their antiholomorphic derivative, with absolute convergence and
invariance under changing the value at the pole.

Source: Demailly, Complex Analytic and Differential Geometry, I §3.A, formula (3.2)
and Corollary (3.4), printed p.21 (blueprint: lem-sfb-cauchy-green-test-function).

Proof plan (the node's punctured-disk argument):
1. By lem-sfb-planar-polar-integration, the truncated reciprocal distance
   `q(c,s)(w) = 1 / ‖w-c‖` on `0 < ‖w-c‖ ≤ s`, zero elsewhere, has integral
   `2πs`. The same formula shows that singletons and circles have area zero.
   Bound the kernel on a compact set by `q(0,s)/π` and apply
   lem-sfb-integrable-majorant-estimate to obtain local integrability.
2. Put `g = (u_x + I*u_y)/2`. It vanishes outside the compact support of `u`,
   and is bounded in norm by some `M` there. Choose a disk of radius `R` centered
   at `z` containing that support. The quotient `F(ζ) = g(ζ)/(z-ζ)`, zero at `z`,
   is bounded by `M*q(z,R)`. The majorant estimate gives absolute convergence.
3. On the annulus `ε ≤ ‖ζ-z‖ ≤ R`, apply lem-sfb-cauchy-green-annulus-formula
   to `v(ζ) = u(ζ)/(z-ζ)`. Direct differentiation gives `dbar(v) = F`.
   The outer boundary term is zero; the inner term is
   `-(1/(2I)) * ∮ u(ζ)/(z-ζ) dζ` with counterclockwise orientation.
4. Parametrize the inner circle by `ζ = z + ε exp(It)`. The annular integral
   becomes `(1/2) * ∫ t in 0..2π, u(z + ε exp(It))`. Its difference from `π*u(z)`
   is bounded by `π` times the modulus of continuity of `u` on the small circle,
   using lem-sfb-integrable-majorant-estimate. This tends to zero as `ε → 0`.
5. The difference between the full integral of `F` and its annular integral is
   bounded by `M * ∫ q(z,ε) = 2πMε`, again by the polar formula and majorant
   estimate; the bounding circles and singleton have area zero.
6. The triangle inequality and the two bounds imply `∫ F = π*u(z)`.
   Divide by `π` for reproduction. Every alternative integrand in the last
   clause agrees almost everywhere, since the exceptional singleton is null;
   integrability and the integral therefore remain unchanged.
-/
theorem cauchyGreen_test_function :
    LocallyIntegrable (fun w : ℂ ↦ 1 / ((Real.pi : ℂ) * w)) volume ∧
      ∀ (u : ℂ → ℂ), ContDiff ℝ ∞ u → HasCompactSupport u → ∀ z : ℂ,
        Integrable (fun ζ : ℂ ↦
          (1 / ((Real.pi : ℂ) * (z - ζ))) *
            ((fderiv ℝ u ζ 1 + I * fderiv ℝ u ζ I) / 2)) volume ∧
        (∫ ζ : ℂ, (1 / ((Real.pi : ℂ) * (z - ζ))) *
          ((fderiv ℝ u ζ 1 + I * fderiv ℝ u ζ I) / 2)) = u z ∧
        ∀ F : ℂ → ℂ,
          (∀ ζ : ℂ, ζ ≠ z → F ζ =
            (1 / ((Real.pi : ℂ) * (z - ζ))) *
              ((fderiv ℝ u ζ 1 + I * fderiv ℝ u ζ I) / 2)) →
          Integrable F volume ∧ (∫ ζ : ℂ, F ζ) = u z := by
  sorry

end Complex
