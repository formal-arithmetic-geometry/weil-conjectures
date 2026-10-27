/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveRepresentationCoordinates
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.AffinePropernessFormalArcTest
import Sheaf.LinearAlgebra.DvrMatrixSmithPowers
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Projective Hilbert--Mumford criterion for SL representations

Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition,
Theorem 2.1; Morrison, arXiv:0810.2340, §2.2, proof of Proposition 1, pp.6--7
(blueprint: lem-sfb-hilbert-mumford-projective-representation).

We use coordinates on the finite-dimensional vector spaces, while allowing their
universes to differ from the field's universe. The group scheme is the recorded
SL of rank dim E. The basis b identifies the recorded projective coordinate space
with the space of lines in V. The action, the equivariant embedding and the induced dual
tautological linearization form one `LinearizedEmbedding`, and the vector lift is
`IsVectorLift` of the coordinate vector of v (def-sfb-projective-representation-linearization),
the interface of lem-sfb-projective-stability-affine-orbit-proper used in step 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.ProjectiveRepresentation

/-- A projective point is stable exactly when every nontrivial one-parameter subgroup
has a negative occurring weight in a nonzero vector lift. Equivalently, the minimum
occurring weight is strictly negative. No characteristic, reducedness or smoothness
of a stabilizer is assumed.

Source: MFK, Theorem 2.1 and Chapter 2, §1, Proposition 2.2;
Morrison §2.2, proof of Proposition 1, pp.6--7
(blueprint: lem-sfb-hilbert-mumford-projective-representation).

Proof, following the five steps of the node:
1. Choose coordinates and the displayed vector lift. The orbit morphism from SL to
   affine vector space is a morphism of affine finite-type schemes
   (def-sc-general-linear-group). By lem-sfb-projective-stability-affine-orbit-proper,
   stability is equivalent to its properness. Use lem-sfb-affine-properness-formal-arc-test.
2. For A = k[[t]], inversion recursively inverts series with nonzero constant term.
   Every nonzero series is t^n times a unit. Least orders in ideals show that A is a
   local PID with nonzero maximal ideal (t), hence a DVR (def-sc-discrete-valuation-ring).
   Its fraction field is k((t)); def-weil-formal-power-series fixes the series operations.
3. Clear denominators in g in SL_r(k((t))) and apply lem-sfb-dvr-matrix-smith-powers.
   Obtain g = P D Q with integral invertible P,Q and D = diag(t^(n_i)). Determinants
   give sum n_i = 0 and det P det Q = 1. With C = diag((det P)^(-1),1,...,1), replace
   P,Q by PC,C^(-1)Q. Both now have determinant one and C commutes with D. A g with
   no integral extension has some n_i nonzero.
4. If the orbit map is not proper, the arc test gives such a g with gv integral.
   Put w(t) = Q(t)v. Then Dw(t) is integral and w(0) is nonzero. The weight basis
   of lem-sfb-gm-representation-weight-basis shows each negative-weight component
   of w(0) is zero. Conjugate diag(z^(n_i)) by Q(0) to obtain a nontrivial subgroup
   whose occurring weights on v are all nonnegative, contradicting the criterion.
   Thus the orbit map is proper and y is stable.
5. Conversely, properness extends any lambda(t) whose action on v has only nonnegative
   weights, since its image vector is integral. The defining representation on E has
   weights summing to zero, not all zero for a nontrivial lambda. One is negative,
   so lambda(t) has a nonintegral diagonal entry in a constant weight basis and cannot
   extend to SL(A), a contradiction. These arguments retain nonreduced Y and finite
   nonreduced stabilizers throughout.
-/
theorem isStable_iff_all_oneParameterSubgroups_negative
    (k : Type u) [Field k] [IsAlgClosed k]
    (E : Type v) [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (hr : 2 ≤ Module.finrank k E)
    (V : Type w) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    (b : Module.Basis (LinearGroupSchemes.Index (Module.finrank k V)) k V)
    (ρ : (specialLinear (k := k) E).X ⟶
      GeneralLinearGroup (LinearGroupSchemes.Index (Module.finrank k V)) k) [IsMonHom ρ]
    (Y : Over (Spec (.of k))) [IsHProjective Y.hom]
    (j : Y ⟶ lines (k := k) V) [IsClosedImmersion j.left]
    (D : LinearizedEmbedding (G := specialLinear (k := k) E) ρ j)
    (y : PGLLinearization.fieldTest k k ⟶ Y) (v : V) (hv : v ≠ 0)
    (hlift : IsVectorLift (Pi.basisFun k (LinearGroupSchemes.Index (Module.finrank k V)))
      j y ⇑(b.repr v)) :
    D.linearization.IsStable k y ↔
      ∀ (lam : StandardGroupSchemes.multiplicative k ⟶ (specialLinear (k := k) E).X)
        [IsMonHom lam], lam ≠ 1 → HasNegativeWeight (restrictedCoaction b ρ lam) v := by
  sorry

end AlgebraicGeometry.ProjectiveRepresentation
