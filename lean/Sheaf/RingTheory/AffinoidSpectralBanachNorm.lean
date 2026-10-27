/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Analysis.Normed.Algebra.Spectrum
import WeilConjectures.RingTheory.TraceFormEtaleField

/-!
# The spectral Banach norm of a reduced affinoid algebra

Source: BGR, Theorem 6.2.4/1; Conrad, Several approaches to non-archimedean
geometry, Theorem 1.2.6(1),(5) and the following paragraph, PDF pp. 6--7
(blueprint: lem-trf-affinoid-spectral-banach-norm).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u v

namespace RestrictedSeries

/-- The supremum over continuous scalar-valued characters is a complete,
power-multiplicative nonarchimedean algebra norm inducing the affinoid topology,
and is bounded above and below by every Tate quotient norm as specified.
The hypothesis on open sets is the quotient topology for Gauss-norm balls;
the restricted-series subring's coefficientwise topology is not used.

Source: BGR, Theorem 6.2.4/1; Conrad, Several approaches to non-archimedean
geometry, Theorem 1.2.6(1),(5) and the following paragraph, PDF pp. 6--7
(blueprint: lem-trf-affinoid-spectral-banach-norm).

Proof (the seven steps of the node):
1. Fix any Tate presentation and its quotient norm. By
   lem-trf-affinoid-quotient-norm-topology it is complete and induces the stated
   topology. By lem-trf-affinoid-supremum-seminorm-calculus the residue fields at
   maximal ideals are finite over K, hence equal to K by algebraic closedness,
   and the residue supremum is bounded by the quotient norm. The quotient norm
   of 1 is at most 1 from its constant lift, and at least 1 by nondegeneracy and
   submultiplicativity. By lem-per-banach-character-norm-bound (Mathlib's
   AlgHom.norm_apply_le_self), residue characters are contractive and continuous.
   Conversely every character fixes K, is onto, and is the residue character of
   its maximal kernel. Thus the character supremum equals the finite residue
   supremum. Nonzero C has a maximal ideal, so the indexing set is nonempty.
2. By lem-trf-affinoid-finite-galois-envelope embed C in a finite product of
   normal affinoid domains B_i, finite over C and over Tate algebras T_i. The
   maximum of their quotient norms makes the product complete. The stated
   bounds on the structure maps bound its C-action. Apply
   lem-trf-affinoid-finite-module-strictness to this finite C-linear injection
   to bound the quotient norm of c by A times the maximum norm of its images.
3. Put F_i = Frac(T_i) and L_i = Frac(B_i). Every element of L_i is beta/t,
   with beta in B_i and nonzero t in T_i: a minimal integral equation for a
   nonzero denominator has nonzero constant term, and expresses its inverse
   with denominator in T_i. Hence choose an F_i-basis e_ik inside B_i. By
   lem-trf-tate-galois-trace-supremum-bound the coordinates Tr(e_ik b) lie in
   T_i. The resulting T_i-linear trace-coordinate map is injective: the trace
   Gram matrix has nonzero determinant by
   lem-sbc-trace-form-nondegenerate-iff-etale-field, since L_i/F_i is finite
   separable, and the adjugate matrix then detects the zero coordinate vector.
4. The finite product of T_i's is complete for the maximum Gauss norm by
   lem-trf-restricted-series-gauss-completion. Apply finite-module strictness
   to the trace-coordinate injection to bound the norm of b by H_i times the
   maximum Gauss norm of its trace coordinates. The trace supremum bound gives
   at most H_i R_i times the residue supremum of b, where R_i is the maximum
   of 1 and the finitely many residue suprema of the basis elements. These
   suprema are finite by lem-trf-affinoid-supremum-seminorm-calculus.
5. Functoriality in lem-trf-affinoid-supremum-seminorm-calculus bounds each
   image's residue supremum by that of c. Combine steps 2 and 4 and enlarge
   the constant to M >= 1. Together with step 1 this gives rho(c) <= norm_q(c)
   <= M rho(c) for the arbitrary presentation. It also gives nondegeneracy.
6. Each character preserves 1, addition, multiplication and scalars. Taking
   suprema in the nonempty bounded family gives normalization at 1, the
   ultrametric inequality, submultiplicativity, scalar homogeneity (including
   zero scalars), and invariance under negation. Power multiplicativity follows
   from the residue-supremum power identity and step 1.
7. A rho-Cauchy sequence is quotient-norm Cauchy by the upper estimate of step 5.
   It has a quotient-norm limit by step 1, which is also a rho-limit by the
   lower estimate. The estimates identify the metric-ball topologies, proving
   completeness and equality with the given affinoid topology. -/
theorem affinoid_spectral_banach_norm
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K]
    (C : Type v) [CommRing C] [Nontrivial C] [IsReduced C]
    [Algebra K C] [TopologicalSpace C]
    (haff : ∃ (r : ℕ)
      (q : (MvPowerSeries.IsRestricted.subring (R := K)
        (fun _ : Fin r ↦ (1 : ℝ))) →+* C),
      Function.Surjective q ∧ q.comp (constants K r) = algebraMap K C ∧
      ∀ U : Set C, IsOpen U ↔ ∀ s, q s ∈ U → ∃ ε : ℝ, 0 < ε ∧
        ∀ t, MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)
          (t.val - s.val) < ε → q t ∈ U) :
    ∃ ρ : AlgebraNorm K C,
      (∀ c : C, ρ c = sSup {x : ℝ | ∃ χ : C →ₐ[K] K, Continuous χ ∧ x = ‖χ c‖}) ∧
      ρ 1 = 1 ∧ IsNonarchimedean ρ ∧ IsPowMul ρ ∧
      @CompleteSpace C ρ.toRingNorm.toNormedRing.toUniformSpace ∧
      ρ.toRingNorm.toNormedRing.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace C) ∧
      ∀ (r : ℕ)
        (q : (MvPowerSeries.IsRestricted.subring (R := K)
          (fun _ : Fin r ↦ (1 : ℝ))) →+* C),
        Function.Surjective q → q.comp (constants K r) = algebraMap K C →
        ∃ M : ℝ, 1 ≤ M ∧ ∀ c : C,
          ρ c ≤ sInf {x : ℝ | ∃ s, q s = c ∧
            x = MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1) s.val} ∧
          sInf {x : ℝ | ∃ s, q s = c ∧
            x = MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1) s.val} ≤
              M * ρ c := by
  sorry

end RestrictedSeries
