/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.Analysis.Normed.Field.Basic
import Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Boundedness of homomorphisms between strict affinoid algebras

Source: Conrad, Several approaches to non-archimedean geometry, Theorem 1.2.6(2),
printed p. 6; Kedlaya, Tate algebras, Proposition 10 and Corollary 11, PDF p. 7
(blueprint: lem-trf-affinoid-homomorphism-bounded).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w

namespace RestrictedSeries

/-- Every unital algebra homomorphism between nonzero strict affinoid algebras with
quotient Gauss norms is bounded and continuous. No injectivity, module finiteness,
reducedness, or separability is required.
Source: Conrad, Theorem 1.2.6(2), printed p. 6; Kedlaya, Proposition 10 and
Corollary 11, PDF p. 7 (blueprint: lem-trf-affinoid-homomorphism-bounded).

Proof:
1. Apply lem-trf-affinoid-polynomial-closed-point-comparison to the zero polynomial
ideal to obtain Noetherianity of each presenting Tate algebra. Its surjective
image is Noetherian by lem-weil-pbc-surjective-image-noetherian, using
 def-weil-pbc-noetherian-ring.
2. For every ideal of either affinoid algebra, choose finitely many generators.
Apply lem-trf-affinoid-finite-module-strictness to its inclusion with the inherited
norm and to the map from the finite free module on these generators. The image
is closed; the zero ideal is included by using zero generators.
3. By lem-trf-affinoid-supremum-seminorm-calculus, each maximal residue field of B
is finite over K. Then lem-trf-noetherian-residue-finite-quotients shows that all
positive powers of maximal ideals have finite-dimensional quotients and their
intersection is zero. Denote this separating family by S.
4. For I in S, put J = f⁻¹(I). The induced K-linear map A/J → B/I is injective.
Hence A/J is finite-dimensional, since B/I is finite-dimensional.
5. Both quotient spaces are Hausdorff by lem-trf-closed-subspace-hausdorff-quotient.
The induced linear map is continuous by lem-sfb-finite-dimensional-linear-map-continuous.
Quotient projections are continuous by lem-sfb-finite-dimensional-quotient-open.
Thus a ↦ f(a) mod I is continuous for every I in S, without assuming continuity of f.
6. If a sequence aⱼ converges to a and f(aⱼ) converges to b, uniqueness of limits
in each Hausdorff quotient B/I implies b - f(a) ∈ I. Separation gives b = f(a).
Apply lem-trf-banach-closed-graph-continuity to the K-linear map underlying f;
the quotient presentations supply completeness of A and B.
7. Apply lem-trf-continuous-linear-map-norm-bound to obtain a positive real D
bounding the norm of f on every a. Nontriviality of the scalar norm is retained.
-/
theorem affinoid_homomorphism_bounded
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [NormedCommRing A] [Nontrivial A] [Algebra K A]
    (B : Type w) [NormedCommRing B] [Nontrivial B] [Algebra K B]
    (hA : IsAffinoidQuotient K A (algebraMap K A))
    (hB : IsAffinoidQuotient K B (algebraMap K B)) (f : A →ₐ[K] B) :
    (∃ D : ℝ, 0 < D ∧ ∀ a : A, ‖f a‖ ≤ D * ‖a‖) ∧ Continuous f := by
  sorry

end RestrictedSeries
