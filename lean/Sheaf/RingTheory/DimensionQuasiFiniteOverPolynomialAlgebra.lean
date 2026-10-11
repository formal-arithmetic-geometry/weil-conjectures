/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Topology.KrullDimension
import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Dimension of a quasi-finite algebra over affine space

Source: Stacks Project, Algebra, Lemma Tag 00QG
(blueprint: lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra).
-/

universe u v

namespace AlgebraicGeometry

/-- A finite-type `k`-algebra with a quasi-finite `k`-algebra map from the polynomial
ring in `n` variables has spectrum of dimension at most `n` (Stacks Project, Tag 00QG).
(blueprint: lem-weil-pbc-dimension-quasi-finite-over-polynomial-algebra)

Proof, step 1: for a prime `q` of `T`, contract it to `p` in the polynomial ring.
The local dimension inequality of Tag 00QF
(`lem-weil-pbc-dimension-inequality-quasi-finite`) bounds `dim T_q` by `dim P_p`.
Choose a maximal ideal `m` containing `p`
(`lem-weil-pbc-proper-ideal-contained-in-maximal`). Chains below `p` are also below `m`
(`lem-weil-pbc-localization-dimension-chains-below-prime`), so `dim P_p ≤ dim P_m = n`
by Tag 00OP (`lem-weil-pbc-polynomial-ring-maximal-localization-dimension`).

Step 2: chains of irreducible closed subsets of `Spec T` correspond, with reversed
inclusions, to chains of primes (`lem-weil-pbc-spec-irreducible-closed-subsets-primes`).
A prime chain ending at `q` has length at most `dim T_q`
(`lem-weil-pbc-localization-dimension-chains-below-prime`), hence at most `n` by step 1.
Take the supremum of chain lengths (`def-kun-topological-krull-dimension`).
For the empty spectrum that supremum is bottom, representing minus infinity. -/
theorem topologicalKrullDim_spec_le_of_quasiFinite_over_mvPolynomial
    (k : Type u) [Field k] (n : ℕ) (T : Type v) [CommRing T] [Algebra k T]
    [Algebra.FiniteType k T] (φ : MvPolynomial (Fin n) k →ₐ[k] T)
    (hφ : letI := φ.toRingHom.toAlgebra
      Algebra.FiniteType (MvPolynomial (Fin n) k) T)
    (hq : letI := φ.toRingHom.toAlgebra
      letI : Algebra.FiniteType (MvPolynomial (Fin n) k) T := hφ
      ∀ q : PrimeSpectrum T, Algebra.IsQuasiFiniteAtPrime (MvPolynomial (Fin n) k) T q) :
    topologicalKrullDim (Spec (CommRingCat.of T)) ≤ (n : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
