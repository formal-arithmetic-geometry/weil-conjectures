/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Noetherian.Defs
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Length
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.CompletionDimensionEquality
import WeilConjectures.RingTheory.LocalCompletionQuotient
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import WeilConjectures.RingTheory.ExistsCoefficientSubring
import Sheaf.RingTheory.RegularCompleteCoefficientCoordinates
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation

/-! # Bennett's local numerical criterion for normal flatness

Source: Cossart--Jannsen--Saito, March 12 2009 preprint, section 2,
Theorem 2.3 (1) iff (2), printed page 29, citing Bennett, Theorem (3)
(blueprint: lem-per-bennett-normal-flat-local-criterion).

The source's degree-wise Hilbert functions become the length functions used here
by one inclusive summation. All lengths are finite under the stated Noetherian
local hypotheses, so `toNat` preserves their values. No reducedness is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal

/-- Bennett's criterion, including zero and nilpotent prime centres.
Source: Cossart--Jannsen--Saito, section 2, Theorem 2.3 (1) iff (2), printed page 29
(blueprint: lem-per-bennett-normal-flat-local-criterion).

Proof plan, following the eleven steps of the DAG node:
1. The regular local quotient A = R/I is a domain (lem-sc-regular-local-domain).
Each G_j = I^j/I^(j+1) is finite (lem-weil-pbc-noetherian-submodule-finite).
Exact localization (lem-weil-pbc-localization-module-exact) identifies its generic
rank r_j with the degree-j Hilbert function of R_I. Write mu_j for its residue dimension.
2. If mu_j = r_j, Nakayama gives a surjection A^r_j onto G_j
(lem-weil-pbc-nakayama-local-generators). Its kernel localizes to zero by
lem-weil-pbc-localization-module-exact and is a submodule of a free module over
the domain A, hence is zero. Thus G_j is free, including rank zero.
3. Maximal-ideal filtrations and lem-weil-pbc-length-additive-short-exact give
h_T = summation g_T. Taking successive differences shows that the required
length equality is equivalent to g_R = summation^[d] r at every degree.
4. Complete R and A at their maximal ideals. The completions are complete Noetherian
local rings with the same residue field, by
lem-weil-pbc-completion-noetherian-quotient-noetherian and
lem-weil-pbc-local-completion-local-ring. By lem-weil-pbc-adic-completion-mod-power
the Hilbert function is unchanged. The completion of A is regular of dimension d
by lem-weil-pbc-completion-regular-local and lem-weil-pbc-completion-dimension-eq.
5. Use lem-weil-pbc-local-completion-quotient and
lem-weil-pbc-completion-exact-finite-modules to identify the completed graded
pieces H_j with the completions of G_j. By
lem-weil-pbc-completion-finite-module-tensor they are D tensor G_j, where D is
the completion of A. By lem-weil-pbc-module-completion-complete their residue
dimensions remain mu_j, and free G_j give free H_j of rank r_j.
6. By lem-weil-pbc-cohen-coefficient-ring-exists choose a coefficient ring in the
completion C of R. Since C contains F it is a coefficient field. By
lem-trf-regular-complete-coefficient-coordinates, D is a power-series ring in d
variables over this field. Lift its parameters to C and apply
lem-weil-pbc-power-series-adic-evaluation. Uniqueness gives a section D into C.
7. Assuming only that G_j is free for j < N, apply
lem-per-split-nilpotent-filtration-graded-piece to C/(IC)^(N+1). The degree-N
maximal-ideal piece has dimension mu_N + sum_{j<N} r_j c_d(N-j), where c_d(q)
counts degree-q monomials in d variables. This does not assume G_N free.
8. Partition monomials by the last variable and interchange finite sums to obtain
(summation^[d] r)(N) = sum_{j<=N} r_j c_d(N-j). The coefficient of r_N is one,
including d = 0, where c_0 is one in degree zero and zero elsewhere.
9. If the whole graded ring is flat, its graded summands are flat and finite,
hence free by lem-weil-pbc-finite-flat-local-free. Steps 7 and 8 give the numerical
equality, including degree zero; step 3 converts it to the length convention.
10. Conversely the numerical equality and steps 7 and 8 imply mu_N = r_N
inductively, starting with G_0 = A. Step 2 gives freeness in each degree.
11. The union of bases of the graded pieces is a basis of their direct sum.
Tensoring an injection with this free module is a direct sum of injections,
hence injective. This is flatness. The argument allows I = 0; at I = maximalIdeal R,
d = 0 and the numerical assertion is the identity.
-/
theorem flat_associatedGraded_iff_hilbertSamuel_eq_iterate_summation
    (F : Type u) [Field F] (R : Type v) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Algebra F R] [Algebra.EssFiniteType F R]
    (I : Ideal R) [I.IsPrime] (hI : I ≤ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ I)] (d : ℕ)
    (hd : ringKrullDim (R ⧸ I) = (d : WithBot ℕ∞)) :
    Module.Flat (R ⧸ I) (associatedGraded I) ↔
      (fun n : ℕ ↦ (Module.length R (R ⧸ IsLocalRing.maximalIdeal R ^ (n + 1))).toNat) =
        (AlgebraicGeometry.HilbertSamuel.summation^[d])
          (fun n : ℕ ↦ (Module.length (Localization.AtPrime I)
            (Localization.AtPrime I ⧸
              IsLocalRing.maximalIdeal (Localization.AtPrime I) ^ (n + 1))).toNat) := by
  sorry

end Ideal
