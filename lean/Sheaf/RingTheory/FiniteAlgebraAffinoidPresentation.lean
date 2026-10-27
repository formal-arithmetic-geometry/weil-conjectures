/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Finite algebras over strict affinoids

Source: Brian Conrad, Several approaches to non-archimedean geometry,
Theorem 1.2.6(3) and Exercise 1.2.4, pp. 5–6
(blueprint: lem-trf-finite-algebra-affinoid-presentation).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RestrictedSeries

/-- A module-finite algebra over an algebra admitting a Tate quotient presentation admits
its own presentation with a complete, nonarchimedean, homogeneous quotient Gauss norm.
The existential `RingNorm` uses the given ring operations on `B`; no norm or topology on
`A` or `B` is assumed. Scalar compatibility of the ring maps means they are `K`-algebra
maps. Source: Conrad, Theorem 1.2.6(3) and Exercise 1.2.4, pp. 5–6
(blueprint: lem-trf-finite-algebra-affinoid-presentation).

Proof (the node's agent reconstruction).
1. Choose finite A-module generators of B (def-weil-finitely-generated-module). They also
   generate it as an algebra. Integrality (lem-weil-pbc-finite-algebra-is-integral) gives
   monic relations of positive degree, because B is nonzero. Lift their coefficients along
   the given surjection from T = K⟨X₁,…,Xᵣ⟩ to A.
2. Choose π with 0 < |π| < 1. The lifted coefficients have finite Gauss norms by
   lem-trf-restricted-series-gauss-completion. Rescale each generator bᵢ to πᴺⁱbᵢ so that
   all coefficients of its rescaled monic relation have norm at most one. This is possible
   because there are only finitely many coefficients and positive exponents. Scaling by
   a nonzero field element preserves the generated A-algebra.
3. Evaluate the polynomial algebra T[Y₁,…,Yₛ] at the rescaled generators
   (def-weil-pbc-mv-polynomial-ring). This is surjective and kills the separate monic
   relations. Factor through their ideal (def-weil-pbc-algebra-hom-quotient), then use
   lem-trf-tate-separated-monic-quotient to obtain a surjection from K⟨X,Y⟩ to B.
4. Its fibres are the cosets of its kernel I, identifying B with K⟨X,Y⟩/I.
   By lem-trf-tate-ideal-best-approximation each coset has a minimizing representative,
   so I is closed. The complete submultiplicative Gauss norm is supplied by
   lem-trf-restricted-series-gauss-completion. Apply lem-trf-banach-closed-ideal-quotient
   and transfer its complete homogeneous quotient norm to B through this identification.
5. Minimizing representatives and the Gauss maximum inequality give the nonarchimedean
   maximum inequality on B. The representative 1 gives norm at most one for the unit;
   nonzeroness and submultiplicativity give norm exactly one. This is an affinoid quotient
   presentation (def-trf-restricted-series-presentation). No injectivity of A → B,
   reducedness, or separability was used.
-/
theorem finite_algebra_affinoid_presentation
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Nontrivial A] [Algebra K A]
    (B : Type w) [CommRing B] [Nontrivial B] [Algebra A B] [Algebra K B]
    [IsScalarTower K A B] [Module.Finite A B]
    (hA : ∃ (r : ℕ)
      (α : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →+* A),
      Function.Surjective α ∧ α.comp (constants K r) = algebraMap K A) :
    ∃ N : RingNorm B,
      @IsAffinoidQuotient K _ _ B { N.toNormedRing, ‹CommRing B› with }
        (algebraMap K B) ∧
      IsNonarchimedean (N : B → ℝ) ∧
      ∀ (c : K) (b : B), N (c • b) = ‖c‖ * N b := by
  sorry

end RestrictedSeries
