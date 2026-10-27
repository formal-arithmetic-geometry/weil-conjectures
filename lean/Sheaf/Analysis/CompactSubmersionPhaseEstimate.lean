module

public import Sheaf.Analysis.MultiIndexPartialDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Sheaf.Analysis.Calculus.CoordinateWeightedAdjoint
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Uniform compact-support estimate for a submersion phase

Source: agent-written nonlinear extension of the integration-by-parts argument of Demailly,
Differential and pseudodifferential operators on manifolds, §1 (1.7) and §3 (3.11), pp.2, 9.
The nonlinear assertion is not stated in those notes.
(blueprint: lem-sfb-compact-submersion-phase-estimate)

Functions on an open set are represented by arbitrary ambient extensions. All smoothness,
support conditions, suprema and integrals concern only the open set. The derivative helper
is the existing coordinate multi-index derivative; the seminorm below expands this node's p_N.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

namespace EuclideanSpace

/-- The maximum, over coordinate multi-indices of order at most N, of the supremum on U
of the absolute value of the corresponding derivative. A single supremum gives the same
number as the finite maximum of the individual suprema. For smooth functions supported
in a compact subset of U this is finite. If the compact support set is empty, all these
values are zero; for empty U the real supremum of the empty set is also zero.
Source: the p_N notation in the agent-written nonlinear extension of Demailly §3 (3.11).
(blueprint: lem-sfb-compact-submersion-phase-estimate) -/
noncomputable def compactSupportDerivativeSeminorm {n : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (N : ℕ)
    (u : EuclideanSpace ℝ (Fin n) → ℂ) : ℝ :=
  sSup {r : ℝ | ∃ α : Fin n → ℕ, (∑ j, α j) ≤ N ∧
    ∃ z ∈ U, r = ‖multiIndexPartialDeriv α u z‖}

/-- Uniform decay of an oscillatory integral with compactly supported smooth amplitude
and a smooth submersion phase. The constant is chosen before the amplitude and frequency.
Source: agent-written nonlinear extension of Demailly, Differential and pseudodifferential
operators on manifolds, §1 (1.7) and §3 (3.11), pp.2, 9.
(blueprint: lem-sfb-compact-submersion-phase-estimate)

Proof plan:
1. Empty C forces u and all its derivatives on U to vanish, so p_N(u) = 0; take A_N = 0.
Otherwise derivatives vanish on U \ C. Compact continuity bounds each derivative on C
by lem-sfb-compact-continuous-norm-bound; only finitely many multi-indices occur.
Their suprema, and p_N(u), are finite and nonnegative. Set V = volume(C). Compactness
makes V finite by lem-sfb-real-compact-supported-integral-bound. Smooth supported
functions are integrable by lem-sfb-continuous-on-compact-integrable.
2. For theta nonzero put g = DH(z)^t theta and q = sum_j g_j^2. Surjectivity of DH
implies q > 0: a preimage w of theta would otherwise give norm(theta)^2 = g dot w = 0.
The coefficients a_j = g_j/q are jointly smooth by
lem-sfb-smooth-nonzero-complex-reciprocal. Set phi_theta = H dot theta,
L_theta = sum_j a_j partial_j and T_theta v = -sum_j partial_j(a_j v).
Then L_theta(phi_theta) = 1 and L_theta(exp(-it phi_theta)) = -it exp(-it phi_theta).
3. For unit theta use lem-sfb-coordinate-weighted-adjoint with scalar ranks, identity
Hermitian metrics and density one, coefficients a_j, and zero constant coefficient.
Its pairing identity gives it integral exp(it phi_theta) v = integral exp(it phi_theta) T_theta v.
Only v requires compact support. Iteration preserves smoothness and support in C,
so (it)^N integral exp(it phi_theta) u = integral exp(it phi_theta) T_theta^N u.
4. Product-rule induction writes T_theta^r u = sum_{|alpha| <= r} c_{r,alpha} partial^alpha u.
Start with c_{0,0} = 1 and absent indices zero; the recursion is
c_{r+1,beta} = -sum_j (partial_j(a_j c_{r,beta}) + a_j c_{r,beta-e_j}).
All coefficients are jointly smooth. The unit sphere is compact by
lem-cbc-euclidean-sphere-compact; its product with C is compact by the finite product-cover
argument. Bound each c_{N,alpha} there using lem-sfb-compact-continuous-norm-bound.
Summing the finitely many bounds yields B_N with |T_theta^N u| <= B_N p_N(u) on C,
uniformly for unit theta. These bounds depend only on U,C,H,N.
5. For t = norm(eta) >= 1 take theta = eta/t. The phase has modulus one.
Apply lem-sfb-integrable-majorant-estimate on C with majorant B_N p_N(u) and divide
by t^N. Since 1+t <= 2t the bound is 2^N V B_N (1+t)^(-N) p_N(u), including N = 0.
6. For t <= 1 use lem-sfb-integrable-majorant-estimate with majorant p_0(u) <= p_N(u).
Since (1+t)^N <= 2^N the bound is 2^N V (1+t)^(-N) p_N(u).
Take A_N = 2^N V max(1,B_N). Zero frequency, zero volume and zero amplitude are included.
-/
theorem compactSubmersion_phase_estimate
    {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (U C : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hC : IsCompact C) (hCU : C ⊆ U)
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k))
    (hH : ContDiffOn ℝ ∞ H U)
    (hsub : ∀ z ∈ U, Function.Surjective (fderiv ℝ H z)) :
    ∀ N : ℕ, ∃ A : ℝ, 0 ≤ A ∧
      ∀ u : EuclideanSpace ℝ (Fin n) → ℂ, ContDiffOn ℝ ∞ u U →
        (∀ z ∈ U, z ∉ C → u z = 0) → ∀ η : EuclideanSpace ℝ (Fin k),
          ‖∫ z in U, Complex.exp (Complex.I * (inner ℝ (H z) η : ℂ)) * u z‖ ≤
            A * (1 + ‖η‖) ^ (-(N : ℤ)) * compactSupportDerivativeSeminorm U N u := by
  sorry

end EuclideanSpace
