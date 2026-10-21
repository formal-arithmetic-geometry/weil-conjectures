/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.RingTheory.TateResidue.DVRResidueCalculus
public import WeilConjectures.RingTheory.TateResidue.ResidueTheorem

/-! # Adelic reciprocity for local Tate residues

Source: Tate, Residues of differentials on curves, §2, R5, and §3, proof of
Theorem 3 and its corollary, pp. 155–157
(blueprint: lem-pc-tate-adelic-reciprocity).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace TateResidue

/-- If the intersection and principal-parts cokernel of a family of DVR subalgebras
are finite-dimensional, every differential has finite residue support and total residue zero.
The principal-parts map is the existing `principalParts`, and the residue is the existing
`localRes`, characterized by `dvr_residue_calculus` through finite-potent commutator traces.

Source: Tate, §2, R5, and §3, proof of Theorem 3 and its corollary, pp. 155–157
(blueprint: lem-pc-tate-adelic-reciprocity).

Proof plan, following the eight steps of the node:
1. Form the restricted product V of the copies of K, its integral part A = product O_i,
   and the diagonal subspace B. Finite nonintegrality makes V a K-module. If I is empty,
   all residues and their sum are empty; otherwise the diagonal map is injective.
2. For each f, the quotient (fA+A)/A injects into the finite sum of (fO_i+O_i)/O_i
   at its nonintegral coordinates. These are finite-dimensional by
   lem-pc-tate-dvr-residue-calculus. Thus A is admissible; B is K-stable.
3. The diagonal identifies A intersect B with the intersection of the O_i. The
   coordinate quotient V to the direct sum of K/O_i is onto with kernel A, and its
   composite with the diagonal is principalParts. Hence V/(A+B) is its cokernel.
4. Apply lem-pc-tate-residue-lattice-identity to A and B. The residues of B, A+B,
   and A intersect B vanish by lem-pc-tate-abstract-residue-calculus, using K-stability
   and the two finite-dimensional hypotheses. Consequently the residue of A is zero.
5. For f dg let S be the union of the finite nonintegrality sets of f and g. Outside
   S the differential is regular, so its local residue vanishes by
   lem-pc-tate-dvr-residue-calculus.
6. Decompose V into its restricted product on I minus S and its finitely many K
   coordinates on S. Successive lattice identities, the zero residue of the zero
   subspace, ambient restriction, and invariance under isomorphisms identify the
   residue of A with the sum of the residue on the complementary integral part and
   the residues of the O_i for i in S. Empty S and empty complement are allowed.
7. Multiplication by f and g preserves that complementary integral part, so its
   residue on f dg is zero. The coordinate residues equal localRes by the identical
   projection commutator trace formulas in the abstract and DVR calculus nodes.
   Evaluation of step 4 now gives zero for the finite sum on S.
8. The symbol presentation of def-weil-pbc-kahler-differentials expresses every
   differential as a finite sum of f dg. Take the finite union of their support bounds
   and interchange the finite sums using k-linearity of localRes. This proves both
   finite support and vanishing total residue, including the zero differential. -/
theorem adelic_reciprocity (k : Type u) (K : Type v) [Field k] [Field K]
    [Algebra k K] (I : Type w) (O : I → Subalgebra k K)
    [∀ i : I, IsDiscreteValuationRing (O i)] [∀ i : I, IsFractionRing (O i) K]
    [∀ i : I, FiniteDimensional k (IsLocalRing.ResidueField (O i))]
    (hfin : ∀ f : K, {i : I | f ∉ O i}.Finite)
    (hH0 : FiniteDimensional k (⨅ i : I, O i : Subalgebra k K))
    (hH1 : FiniteDimensional k
      ((Π₀ i : I, K ⧸ (O i).toSubmodule) ⧸ LinearMap.range (principalParts O hfin)))
    (ξ : KaehlerDifferential k K) :
    (Function.support fun i : I ↦ localRes (O i) ξ).Finite ∧
      ∑ᶠ i : I, localRes (O i) ξ = 0 := by
  sorry

end TateResidue
