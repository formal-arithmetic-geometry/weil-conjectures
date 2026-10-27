module

public import Sheaf.Geometry.Manifold.BundleSobolevSpace
public import Mathlib.Data.Matrix.Mul

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Compact derivative bounds for smooth weighted composition

Source: the agent-written Euclidean auxiliary estimate and its six-step proof in the DAG;
Demailly, Hodge theory, Part I §3.A–3.B is an inherited, locally unavailable motivation,
not a verified source of this formula.
(blueprint: lem-sfb-weighted-composition-derivative-bound)

Maps on open sets are represented by arbitrary ambient extensions. Smoothness is required
only on the given open sets, so all coordinate derivatives there are independent of these
extensions. Norms are Euclidean, including in dimension zero. The two definitions below
expand the weighted composition and the compact derivative maximum in this same estimate.
-/

@[expose] public section

set_option autoImplicit false

open scoped ContDiff

namespace EuclideanSpace

/-- The coordinate formula `T_{A,g} f(z) = A(z) f(g(z))`, with its Euclidean target norm.
Source: agent-written auxiliary estimate in the DAG, definition of `T_{A,g}`.
(blueprint: lem-sfb-weighted-composition-derivative-bound) -/
noncomputable def matrixWeightedComposition {d m q r : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin r) (Fin q) ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin q))
    (z : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 ((A z).mulVec (f (g z)))

/-- The supremum of Euclidean norms of coordinate derivatives of orders at most `k` on `S`.
For smooth maps near compact `S`, this is precisely the finite maximum of the individual
compact suprema. The real supremum of the empty set is zero. Each scalar partial is the
existing ordered partial `BundleSobolev.multiPartial`; no derivatives are taken within `S`.
Source: agent-written auxiliary estimate in the DAG, displayed compact derivative maximum.
(blueprint: lem-sfb-weighted-composition-derivative-bound) -/
noncomputable def compactCoordinateDerivativeSup {d q : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d))) (k : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin q)) : ℝ :=
  sSup {t : ℝ | ∃ α : Fin d → ℕ, (∑ j, α j) ≤ k ∧
    ∃ z ∈ S, t = ‖WithLp.toLp 2
      (fun a : Fin q ↦ BundleSobolev.multiPartial α (fun y ↦ f y a) z)‖}

/-- Smooth matrix-weighted composition is smooth, and each compact finite coordinate-derivative
maximum is bounded by that of the input on the image compact, with a positive constant
chosen independently of the input function.
Source: agent-written Euclidean auxiliary estimate in the DAG, not an assertion verified
in the unavailable inherited Demailly reference, Part I §3.A–3.B.
(blueprint: lem-sfb-weighted-composition-derivative-bound)

Proof plan:
1. Write H_a = ∑ b, A_ab (f_b ∘ g). The sum, product and composition clauses of
   lem-sfb-real-smooth-differentiation give smoothness. Evaluation of the smooth differential
   on a fixed coordinate vector shows that every repeated coordinate derivative is smooth.
   All assertions are local on the open domains, with no smooth extension across a boundary.
2. Apply lem-sfb-real-second-derivative-symmetry to each smooth scalar derivative.
   Adjacent coordinate derivatives commute; sorting any derivative word gives the ordered
   multi-index convention, including ∂_i ∂^β = ∂^(β+e_i).
3. Induct on |α| to obtain coefficients c_{αβab}, smooth and independent of f, such that
   ∂^α H_a = ∑ b ∑ |β|≤|α|, c_{αβab} (∂^β f_b) ∘ g. Start with c_{0,0,ab}=A_ab.
   For α≠0 choose i with α_i>0 and γ=α-e_i. Product and chain rules from
   lem-sfb-real-smooth-differentiation give
   c_{αβab}=∂_i c_{γβab}+∑ j:β_j>0, c_{γ,β-e_j,ab} ∂_i g_j,
   setting coefficients beyond their allowed orders to zero. Step 2 sorts the derivatives.
4. If S is empty take C=1. Otherwise there are finitely many α,β of order at most k.
   Zero-extend each coefficient outside O; it remains continuous on S. Apply
   lem-sfb-compact-continuous-norm-bound and take a finite maximum with 1 to obtain M≥1
   bounding all coefficients. This M depends only on A,g,S,k, before f is chosen.
5. The image g(S) is compact by continuity. Each derivative of f is continuous there,
   since it is smooth on P. The same compact norm bound shows the input maximum P_f
   is finite and nonnegative. Every scalar component is bounded by its Euclidean norm,
   hence by P_f. This does not require unique differentiability of the image compact.
6. Let N be the number of m-dimensional multi-indices of order at most k. The expansion
   gives |∂^α H_a|≤qNMP_f, and the Euclidean norm is at most the sum of absolute
   components. Thus ‖∂^α H‖≤rqNMP_f. Take C=1+rqNM and take suprema and maxima.
   Empty sums cover q=0 or r=0 with C=1; d=0 allows only α=0; m=0 gives N=1;
   k=0 uses the same expansion without differentiation.
-/
theorem matrixWeightedComposition_compact_derivative_bound {d m q r : ℕ}
    (O : Set (EuclideanSpace ℝ (Fin d))) (P : Set (EuclideanSpace ℝ (Fin m)))
    (hO : IsOpen O) (hP : IsOpen P)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin r) (Fin q) ℝ)
    (hgP : Set.MapsTo g O P) (hg : ContDiffOn ℝ ∞ g O)
    (hA : ∀ (a : Fin r) (b : Fin q), ContDiffOn ℝ ∞ (fun z ↦ A z a b) O) :
    (∀ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin q),
      ContDiffOn ℝ ∞ f P → ContDiffOn ℝ ∞ (matrixWeightedComposition A g f) O) ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S → S ⊆ O → ∀ k : ℕ,
      ∃ C : ℝ, 0 < C ∧
        ∀ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin q),
          ContDiffOn ℝ ∞ f P →
            compactCoordinateDerivativeSup S k (matrixWeightedComposition A g f) ≤
              C * compactCoordinateDerivativeSup (g '' S) k f := by
  sorry

end EuclideanSpace
