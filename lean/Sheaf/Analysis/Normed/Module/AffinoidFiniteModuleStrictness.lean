module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Closed images and norm bounds for finite affinoid modules

Source: Kedlaya, A little p-adic functional analysis (part 2 of 2), Lemma 1, p. 1;
Bosch, Lectures on Formal and Rigid Geometry (2008), section 1.4, Proposition 2(i),
and the Banach open mapping theorem
(blueprint: lem-trf-affinoid-finite-module-strictness).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v w x

namespace RestrictedSeries

/-- Every linear map of finite Banach modules with bounded scalar actions over a nonzero
Tate quotient is continuous with closed image; injectivity gives a uniform norm lower bound.
Source: Kedlaya, A little p-adic functional analysis (part 2 of 2), Lemma 1, p. 1,
with its finite-generator/open-mapping corollary; Bosch (2008), section 1.4, Proposition 2(i)
(blueprint: lem-trf-affinoid-finite-module-strictness).

Proof:
1. Apply lem-trf-affinoid-polynomial-closed-point-comparison to the zero polynomial ideal
   over K to obtain Noetherianity of the restricted-series ring. Pull ideals back along
   the given surjection and push their finite generators down to prove A Noetherian
   (def-weil-pbc-noetherian-ring). Finite powers of the Banach ring A are complete in the
   maximum norm by coordinatewise convergence. If either module is zero, the map is zero
   with closed image, and an injective such map has zero source, so H = 1 works.
2. Choose finite generators e_i of M (def-weil-finitely-generated-module). The scalar-action
   bound makes the surjection A^s → M continuous. Apply
   lem-trf-banach-surjective-bounded-lifts to get representatives with coefficient norms
   bounded by L times the norm of m. The action bound on N then bounds the norm of u(m)
   by c_N L max_i ‖u(e_i)‖ times ‖m‖. Apply this to differences to prove continuity.
3. Let S be the image and B its closure in N. B is an A-submodule by continuity of addition,
   negation and each scalar action, and it is complete by closedness. If B is zero, S = B.
   Otherwise lem-weil-pbc-noetherian-submodule-finite supplies finitely many generators b_i.
   The associated map A^t → B is continuous; bounded lifts give coefficient bound L_B.
   Fix 0 < θ < 1 and choose f_i in S within θ/(c_N L_B) of b_i. For x_0 = x in B,
   express x_j = ∑ a_ji b_i with max_i ‖a_ji‖ ≤ L_B ‖x_j‖ and set
   x_(j+1) = x_j - ∑ a_ji f_i. Then ‖x_(j+1)‖ ≤ θ ‖x_j‖. Thus each series
   ∑_j a_ji converges in A: its tails have norm at most L_B θ^p ‖x‖. Telescoping and
   continuity of scalar actions yield x = ∑_i (∑_j a_ji) f_i in S. Hence S = B is closed.
4. If u is injective, its image is a Banach K-space by step 3. The continuous surjective
   corestriction M → S has bounded lifts (lem-trf-banach-surjective-bounded-lifts).
   For s = u(m), injectivity identifies the bounded preimage with m, giving the required H.
-/
theorem affinoid_finite_module_strictness
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [NormedCommRing A] [Nontrivial A] [Algebra K A]
    (hA : IsAffinoidQuotient K A (algebraMap K A))
    (M : Type w) [NormedAddCommGroup M] [NormedSpace K M] [IsUltrametricDist M]
    [CompleteSpace M] [Module A M] [IsScalarTower K A M] [Module.Finite A M]
    (N : Type x) [NormedAddCommGroup N] [NormedSpace K N] [IsUltrametricDist N]
    [CompleteSpace N] [Module A N] [IsScalarTower K A N] [Module.Finite A N]
    (hM : ∃ c : ℝ, 0 < c ∧ ∀ (a : A) (m : M), ‖a • m‖ ≤ c * ‖a‖ * ‖m‖)
    (hN : ∃ c : ℝ, 0 < c ∧ ∀ (a : A) (n : N), ‖a • n‖ ≤ c * ‖a‖ * ‖n‖)
    (u : M →ₗ[A] N) :
    Continuous u ∧ IsClosed (Set.range u) ∧
      (Function.Injective u → ∃ H : ℝ, 0 < H ∧ ∀ m : M, ‖m‖ ≤ H * ‖u m‖) := by
  sorry

end RestrictedSeries
