module

public import Mathlib.Data.NNReal.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Uniform partial Fourier decay for compact spatial symbol families

Source: Demailly, Hodge AMS, Part I §3.B, (3.4)--(3.5), Proposition 3.7, pp.12--13;
supplemental Differential and pseudodifferential operators on manifolds, §3, (3.11)
and the estimates after (3.15), pp.9--11. The external-parameter extension is the
agent-written supporting argument recorded in the DAG.
(blueprint: lem-sfb-parameter-symbol-partial-fourier-decay)

Matrices are complex-linear maps between Euclidean spaces, with operator norm. The
helpers expand the three-block coordinate derivatives and the displayed integral.
The finite sets and constants precede the symbol and its bounds, expressing uniformity.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

namespace EuclideanSpace

/-- Mixed real coordinate derivatives in the three blocks `(x, z, ξ)`. Frequency
coordinates are differentiated first, then `z`, then `x`, each in increasing order.
For smooth functions this is the usual commuting mixed partial derivative.
Source: Demailly, Hodge AMS I §3.B, symbol estimates (3.4)--(3.5), with external parameters.
(blueprint: lem-sfb-parameter-symbol-partial-fourier-decay) -/
noncomputable def parameterSymbolDeriv {d m p q : ℕ}
    (α : Fin d → ℕ) (γ β : Fin m → ℕ)
    (b : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
  (List.ofFn (fun j : Fin d ↦ List.replicate (α j) j)).flatten.foldr
    (fun j g ↦ fun t ↦ fderiv ℝ (fun x ↦ g (x, t.2)) t.1 (single j 1))
    ((List.ofFn (fun j : Fin m ↦ List.replicate (γ j) j)).flatten.foldr
      (fun j g ↦ fun t ↦
        fderiv ℝ (fun z ↦ g (t.1, z, t.2.2)) t.2.1 (single j 1))
      ((List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten.foldr
        (fun j g ↦ fun t ↦
          fderiv ℝ (fun ξ ↦ g (t.1, t.2.1, ξ)) t.2.2 (single j 1)) b))

/-- The partial Fourier integral in `z`, with phase `exp (-i z·η)` and normalization
`(2π)^(-m)`. Convergence is asserted by the theorem below, rather than assumed here.
Source: Demailly, Differential and pseudodifferential operators, §3, (3.11), rescaled
from the source's `2π` Fourier convention to the displayed convention of the node.
(blueprint: lem-sfb-parameter-symbol-partial-fourier-decay) -/
noncomputable def parameterSymbolPartialFourier {d m p q : ℕ}
    (b : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (t : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
  (2 * (Real.pi : ℂ)) ^ (-(m : ℤ)) •
    ∫ z : EuclideanSpace ℝ (Fin m),
      Complex.exp (-Complex.I * (inner ℝ z t.2.1 : ℂ)) • b (t.1, z, t.2.2)

/-- Compact spatial symbol bounds give joint smoothness, the mixed derivative
formula, and rapid partial Fourier decay with a finite-seminorm bound uniform over
all symbols with the fixed supports. The prefactors and finite lists are independent
of both the symbol `b` and the supplied nonnegative input constants `C`.
Source: Demailly, Hodge AMS I §3.B, (3.4)--(3.5), Proposition 3.7, pp.12--13;
Differential and pseudodifferential operators, §3, (3.11), estimates after (3.15),
pp.9--11; external-parameter extension supplied by the DAG argument.
(blueprint: lem-sfb-parameter-symbol-partial-fourier-decay)

Proof plan:
1. If either matrix rank is zero, all conclusions hold with zero constants.
Otherwise smoothness and fixed compact z-support give entrywise integrability by
lem-sfb-continuous-compact-support-integrable. The norm majorant, finite coordinate
linearity and scalar-function integral identity from
lem-sfb-vector-integral-majorant-linearity and lem-sfb-euclidean-bochner-integral-calculus
give the matrix integral and its absolute convergence. Outside Lx its integrand is zero.
2. On a relatively compact parameter ball, every parameter derivative of
exp(-i z·η)b has an integrable majorant M times the indicator of Lz. Polynomial z factors
are bounded on Lz, and the ξ weights are bounded on the ball. The next derivative has
the same property. Apply lem-sfb-dominated-integral-frechet-derivative successively to
these finite-dimensional derivative arrays; lem-sfb-continuous-on-compact-integrable
supplies integrability of the indicator majorants.
3. Induction identifies every derivative of the integral with the integral of the
derivative. The derivative integrals are continuous by step 2, proving joint smoothness.
Evaluation on coordinate vectors commutes with integration by the coordinate linearity
in lem-sfb-euclidean-bochner-integral-calculus. Direct differentiation gives exactly
the factor (-i z)^δ, with no x or ξ derivative of the phase.
4. Apply lem-sfb-scalar-integrable-integration-by-parts entrywise in each z direction.
All three products are continuous and compactly supported, so their integrability and
the differentiability-on-support hypotheses hold. Twice in each direction gives the
multiplier -η_j² for the second derivative. Iterate to move (1-Δ_z)^N onto
(-i z)^δ ∂x^α ∂ξ^β b, with multiplier (1+|η|²)^N on the Fourier integral.
5. Expand this differential operator and use Leibniz. Only finitely many z derivatives
γ of order at most 2N occur, with the same α and β. Bounded monomials on Lz and the
input estimates bound its norm by A times their finite sum times
(1+|ξ|)^(r-|β|) times the indicator of Lz. The integral norm majorant gives an additional
factor volume(Lz), finite by lem-sfb-continuous-on-compact-integrable.
6. Choose N = ceil(L/2). Since (1+u)² ≤ 2(1+u²), replace
(1+|η|²)^(-N) by 2^N (1+|η|)^(-L). Absorb all fixed factors into K.
The lists Γ and constants K depend only on the fixed indices, dimensions and supports,
so work simultaneously for every b and every supplied C. Empty supports, L=0 and
negative r are included; all frequency weights have strictly positive bases.
-/
theorem parameterSymbol_partialFourier_decay
    (d m p q : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) (r : ℤ)
    (Lx : Set (EuclideanSpace ℝ (Fin d))) (Lz : Set (EuclideanSpace ℝ (Fin m)))
    (hLx : IsCompact Lx) (hLz : IsCompact Lz) :
    ∃ (Γ : (Fin d → ℕ) → (Fin m → ℕ) → (Fin m → ℕ) → ℕ →
        Finset (Fin m → ℕ))
      (K : (Fin d → ℕ) → (Fin m → ℕ) → (Fin m → ℕ) → ℕ → NNReal),
    ∀ (b : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin m) →
        EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q))
      (C : (Fin d → ℕ) → (Fin m → ℕ) → (Fin m → ℕ) → NNReal),
      ContDiff ℝ ∞ b →
      (∀ x z ξ, x ∉ Lx ∨ z ∉ Lz → b (x, z, ξ) = 0) →
      (∀ α γ β x z ξ, ‖parameterSymbolDeriv α γ β b (x, z, ξ)‖ ≤
        (C α γ β : ℝ) * (1 + ‖ξ‖) ^ (r - (∑ j, β j : ℕ))) →
      (∀ x η ξ, Integrable (fun z : EuclideanSpace ℝ (Fin m) ↦
        Complex.exp (-Complex.I * (inner ℝ z η : ℂ)) • b (x, z, ξ)) volume) ∧
      ContDiff ℝ ∞ (parameterSymbolPartialFourier b) ∧
      (∀ x η ξ, x ∉ Lx → parameterSymbolPartialFourier b (x, η, ξ) = 0) ∧
      (∀ α δ β x η ξ,
        parameterSymbolDeriv α δ β (parameterSymbolPartialFourier b) (x, η, ξ) =
          (2 * (Real.pi : ℂ)) ^ (-(m : ℤ)) •
            ∫ z : EuclideanSpace ℝ (Fin m),
              (Complex.exp (-Complex.I * (inner ℝ z η : ℂ)) *
                ∏ j, (-Complex.I * (z j : ℂ)) ^ (δ j)) •
                  parameterSymbolDeriv α 0 β b (x, z, ξ)) ∧
      (∀ α δ β (L : ℕ) x η ξ,
        ‖parameterSymbolDeriv α δ β (parameterSymbolPartialFourier b) (x, η, ξ)‖ ≤
          ((K α δ β L : ℝ) * ∑ γ ∈ Γ α δ β L, (C α γ β : ℝ)) *
            (1 + ‖η‖) ^ (-(L : ℤ)) * (1 + ‖ξ‖) ^ (r - (∑ j, β j : ℕ))) := by
  sorry

end EuclideanSpace
