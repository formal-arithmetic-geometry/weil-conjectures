module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Derivatives of a dilated smooth cutoff

Source: Demailly, Differential and pseudodifferential operators on manifolds, §3.7,
printed p.7, scaled-cutoff argument (not available locally); the complete supporting
argument is recorded in the DAG.
(blueprint: lem-sfb-symbol-cutoff-scaled-derivatives)

The multi-index derivative is Mathlib's iterated real Fréchet derivative evaluated on
coordinate unit vectors, each repeated with its prescribed multiplicity in increasing
coordinate order. No new derivative notion is introduced. For smooth functions this is
the usual coordinate partial derivative, including the original function at order zero.
-/

@[expose] public section

set_option autoImplicit false

open scoped ContDiff

namespace EuclideanSpace

/-- A fixed smooth cutoff, zero on the unit closed ball and one outside the radius-two
open ball, has uniform scaled coordinate derivative bounds and annular derivative support.
Source: Demailly, Differential and pseudodifferential operators on manifolds, §3.7,
printed p.7 (unavailable locally); the agent-written argument below supplies the proof.
(blueprint: lem-sfb-symbol-cutoff-scaled-derivatives)

Proof plan:
1. For R ≥ 1 the map L_R(x) = R⁻¹ • x is continuous real-linear. Apply
lem-sfb-real-smooth-differentiation to obtain smoothness of θ ∘ L_R. Induct on the
ordered list of coordinate directions: the chain rule contributes one factor R⁻¹ at
each step, giving ∂^γ(θ ∘ L_R)(x) = R^(-|γ|) (∂^γ θ)(L_R(x)). Coordinate derivatives
are smooth since evaluation of the smooth differential on a fixed unit vector is linear.
2. The cutoff values give θ(L_R(x)) = 0 for ‖x‖ ≤ R. On the open regions ‖x‖ < R
and ‖x‖ > 2R the dilated function is constant. Difference quotients show that its first
coordinate derivatives vanish there; induction gives the same for every positive order.
At R = 1 this also proves that positive derivatives of θ vanish outside the unit annulus.
3. By lem-sfb-finite-dimensional-normed-proper the radius-two closed ball is compact.
Each derivative is continuous, so lem-sfb-compact-continuous-norm-bound bounds it there.
There are finitely many γ of total order at most n, since each entry is at most n.
Take C_n to be the maximum of 1 and these finitely many bounds. Outside this ball,
θ = 1 and every positive derivative is zero, so C_n bounds all these derivatives globally.
4. Take A_n = 2^n C_n ≥ 1. For k = |γ| ≤ n the scaling identity gives the bound
C_n R^(-k). Since R ≥ 1, (1 + R)/R ≤ 2, so
R^(-k) ≤ 2^k (1 + R)^(-k) ≤ 2^n (1 + R)^(-k). This gives the required estimate
uniformly in R, including k = 0 and n = 0, together with the support assertions above.
-/
theorem exists_dilatedCutoff_derivative_bounds
    (m : ℕ) (hm : 1 ≤ m) (θ : EuclideanSpace ℝ (Fin m) → ℝ)
    (hθ : ContDiff ℝ ∞ θ)
    (hzero : ∀ ξ : EuclideanSpace ℝ (Fin m), ‖ξ‖ ≤ 1 → θ ξ = 0)
    (hone : ∀ ξ : EuclideanSpace ℝ (Fin m), 2 ≤ ‖ξ‖ → θ ξ = 1) :
    (∀ R : ℝ, 1 ≤ R → ContDiff ℝ ∞ (fun ξ ↦ θ (R⁻¹ • ξ))) ∧
    (∀ n : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ R : ℝ, 1 ≤ R → ∀ γ : Fin m → ℕ, (∑ j, γ j) ≤ n →
        ∀ ξ : EuclideanSpace ℝ (Fin m),
          ‖iteratedFDeriv ℝ
            (List.ofFn (fun j : Fin m ↦ List.replicate (γ j) j)).flatten.length
            (fun x ↦ θ (R⁻¹ • x)) ξ
            (fun i ↦ EuclideanSpace.single
              ((List.ofFn (fun j : Fin m ↦ List.replicate (γ j) j)).flatten.get i) 1)‖ ≤
            A * (1 + R) ^ (-((∑ j, γ j) : ℤ))) ∧
    (∀ R : ℝ, 1 ≤ R → ∀ ξ : EuclideanSpace ℝ (Fin m),
      ‖ξ‖ ≤ R → θ (R⁻¹ • ξ) = 0) ∧
    (∀ R : ℝ, 1 ≤ R → ∀ γ : Fin m → ℕ, 0 < (∑ j, γ j) →
      ∀ ξ : EuclideanSpace ℝ (Fin m), ¬ (R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * R) →
        iteratedFDeriv ℝ
          (List.ofFn (fun j : Fin m ↦ List.replicate (γ j) j)).flatten.length
          (fun x ↦ θ (R⁻¹ • x)) ξ
          (fun i ↦ EuclideanSpace.single
            ((List.ofFn (fun j : Fin m ↦ List.replicate (γ j) j)).flatten.get i) 1) = 0) := by
  sorry

end EuclideanSpace
