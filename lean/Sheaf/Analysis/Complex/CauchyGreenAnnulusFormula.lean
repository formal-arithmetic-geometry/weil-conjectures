module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Cauchy–Green formula on a closed annulus

Source: the agent polar-coordinate proof in
Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean, lines 482–494;
Demailly, Complex Analytic and Differential Geometry, I §3.A, formula (3.2),
uses this nonsingular annulus input (blueprint: lem-sfb-cauchy-green-annulus-formula).
-/

@[expose] public section

open MeasureTheory

namespace Complex

/-- Cauchy–Green on a closed annulus for continuous real coordinate partials.
The total functions `v`, `vx`, `vy` are arbitrary extensions of the function and
its two partial derivatives from the open set `V`; only their values on `V` matter.
The integrand `(vx z + I * vy z) / 2` is the antiholomorphic derivative.
`CircleIntegrable` asserts absolute integrability along the circle; `circleIntegral`
uses the counterclockwise parametrization `c + s * exp (t * I)`, from `0` to `2 * π`.

Source: agent proof based on Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean,
lines 482–494; Demailly, Complex Analytic and Differential Geometry, I §3.A,
formula (3.2) (blueprint: lem-sfb-cauchy-green-annulus-formula).

Proof plan:
1. Use lem-sfb-continuous-partials-frechet-criterion to obtain the continuous real
   differential `Dv(z)[h] = vx(z) * re(h) + vy(z) * im(h)` on `V`. The bar derivative
   is continuous as well; no complex differentiability is assumed.
2. The annulus is compact. By lem-sfb-continuous-on-compact-integrable its continuous
   bar derivative is integrable. The circle pullbacks and their tangent-weighted
   versions are continuous on compact angle intervals, hence absolutely integrable.
3. On `Q = [r,R] × [-π,π]` put `Φ(ρ,t) = c + ρ * exp (t * I)`, `w = v ∘ Φ`,
   `B = I * ρ * exp (t * I) * w`, and `P = exp (t * I) * w`. The pointwise rules
   of lem-sfb-real-smooth-differentiation give
   `B_ρ - P_t = ρ * (I * vx ∘ Φ - vy ∘ Φ) = 2 * I * ρ * dbar(v) ∘ Φ`.
4. Apply lem-sfb-rectangle-divergence-integral to `B` and `-P` on `Q`. Continuity
   and compact integrability give its hypotheses. The two angle edges cancel
   since `exp (π * I) = exp (-π * I)`, leaving the outer minus inner integrals.
5. Apply lem-sfb-planar-polar-integration to the bar derivative extended by zero
   outside the annulus. The polar Jacobian is `ρ`, and the two angle edges have
   measure zero. Thus the rectangle's area integral is `2 * I` times the stated one.
6. Periodicity moves the angle interval `[-π,π]` to `[0,2π]`. The derivative of the
   circle parametrization is `I * s * exp (t * I)`, identifying both boundary terms
   with counterclockwise circle integrals. Divide by the nonzero scalar `2 * I`.
-/
theorem cauchyGreen_annulus_formula
    (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (V : Set ℂ) (hV : IsOpen V)
    (hA : {z : ℂ | r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ R} ⊆ V)
    (v vx vy : ℂ → ℂ)
    (hvx : ∀ z ∈ V,
      HasDerivAt (fun x : ℝ ↦ v ((x : ℂ) + (z.im : ℂ) * I)) (vx z) z.re)
    (hvy : ∀ z ∈ V,
      HasDerivAt (fun y : ℝ ↦ v ((z.re : ℂ) + (y : ℂ) * I)) (vy z) z.im)
    (hcx : ContinuousOn vx V) (hcy : ContinuousOn vy V) :
    IntegrableOn (fun z ↦ (vx z + I * vy z) / 2)
        {z : ℂ | r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ R} ∧
      CircleIntegrable v c R ∧ CircleIntegrable v c r ∧
      (∫ z in {z : ℂ | r ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ R}, (vx z + I * vy z) / 2) =
        (1 / (2 * I)) * (circleIntegral v c R - circleIntegral v c r) := by
  sorry

end Complex
