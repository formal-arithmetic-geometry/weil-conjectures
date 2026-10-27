module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Quotient Gauss norms on Banach quotients of Tate algebras

Source: Bosch, Lectures on Formal and Rigid Geometry, Section 1.4,
Proposition 4(i)--(ii), printed p. 23, and the Banach open mapping alternative
following Proposition 19, printed p. 31
(blueprint: lem-trf-affinoid-quotient-norm-topology).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace RestrictedSeries

/-- A continuous surjective Tate presentation gives a complete quotient algebra norm
and the quotient topology, with two positive bounds comparing it to the given norm.
Source: Bosch, Section 1.4, Proposition 4(i)--(ii), printed p. 23, and the Banach
open mapping alternative following Proposition 19, printed p. 31
(blueprint: lem-trf-affinoid-quotient-norm-topology).

The continuity hypothesis is written using Gauss balls, so it uses the Gauss topology
rather than the coefficientwise topology inherited from formal power series.
Scalar compatibility with `constants` expresses that the ring map is a K-algebra map.
The conclusion uses the metric and topology constructed from the actual algebra norm.

Proof (the node's seven steps):
1. Apply lem-trf-restricted-series-gauss-completion to get the complete Gauss norm
   on restricted series. Taking suprema of coefficient norms proves scalar homogeneity,
   including the zero scalar, so source and target are Banach K-vector spaces.
2. Apply lem-trf-continuous-linear-map-norm-bound, namely ContinuousLinearMap.bound,
   to obtain B > 0 with norm(q f) ≤ B norm(f). Apply
   lem-trf-banach-surjective-bounded-lifts, namely
   ContinuousLinearMap.exists_preimage_norm_le, to obtain A > 0 and bounded lifts.
3. Surjectivity makes each set of lift norms nonempty, and zero bounds it below.
   Its infimum N(c) admits arbitrarily close approximate lifts. Taking infima in
   the first bound gives norm(c) ≤ B N(c); the bounded lift gives N(c) ≤ A norm(c).
   The zero lift gives N(0) = 0, and the first bound proves definiteness.
4. Negation bijects lift sets isometrically. Nonzero scalar multiplication bijects
   lift sets with norms scaled by the scalar norm, proving homogeneity; the zero
   scalar follows from N(0) = 0. Approximate lifts of c and d and the source's
   ultrametric inequality give N(c+d) ≤ max(N(c), N(d)) by letting the error tend to zero.
5. Products of approximate lifts give N(cd) ≤ N(c)N(d), again letting the error
   tend to zero. The lift 1 gives N(1) ≤ 1. Nontriviality and definiteness give
   N(1) > 0, while submultiplicativity gives N(1) ≤ N(1)^2, hence N(1) = 1.
6. For every t > 0, the image of a Gauss ball of radius t is the N-ball of radius t:
   one inclusion uses the infimum bound and the other uses approximate lifts.
   Translation proves the same at every centre. Thus q is continuous, open and
   surjective for the N-topology, proving the stated open-set quotient criterion.
7. The two positive bounds give the same topology for N and the original norm.
   An N-Cauchy sequence is Cauchy for the original norm by the B-bound; its limit
   in the given Banach algebra is also its N-limit by the A-bound. Metric-space
   completeness follows. No infimum is required to be attained. -/
theorem affinoid_quotient_norm_topology
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (r : ℕ) (C : Type v) [NormedCommRing C] [Nontrivial C]
    [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]
    (q : (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →+* C)
    (hscalar : q.comp (constants K r) = algebraMap K C)
    (hsurj : Function.Surjective q)
    (hcont : ∀ s, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ t, MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)
        (t.val - s.val) < δ → ‖q t - q s‖ < ε) :
    ∃ N : AlgebraNorm K C,
      (∀ c : C, N c = sInf {a : ℝ | ∃ s, q s = c ∧
        a = MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1) s.val}) ∧
      N 1 = 1 ∧
      (∀ c d : C, N (c + d) ≤ max (N c) (N d)) ∧
      @CompleteSpace C N.toRingNorm.toNormedRing.toUniformSpace ∧
      (∀ U : Set C,
        @IsOpen C N.toRingNorm.toNormedRing.toUniformSpace.toTopologicalSpace U ↔
          ∀ s, q s ∈ U → ∃ ε : ℝ, 0 < ε ∧
            ∀ t, MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)
              (t.val - s.val) < ε → q t ∈ U) ∧
      ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
        ∀ c : C, N c ≤ A * ‖c‖ ∧ ‖c‖ ≤ B * N c := by
  sorry

end RestrictedSeries
