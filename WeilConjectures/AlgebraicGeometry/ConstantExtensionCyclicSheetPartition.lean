/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionSheetHeartData

/-! # The point partition of cyclic constant-extension sheets

Source: Deligne, Weil II, (1.1.7) and paragraph after (1.1.10), pp. 150--152.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- The underlying ranges of the prescribed cyclic sheets form a partition.
Source: Deligne, Weil II, paragraph after (1.1.10), p. 152, with the semilinear
Frobenius convention of (1.1.7), p. 150.
(blueprint: lem-zl-constant-extension-cyclic-sheet-partition).

Proof: write E = k_m and gamma for inverse q-Frobenius on k. The evaluation splitting
E tensor_{k_0} k = product_(sigma:E -> k) k, with t tensor b mapping to sigma(t)b,
identifies the base-changed constant factor with disjoint copies of Spec k. Pulling
these factors back along X_0 gives disjoint subsets covering the actual fibre Y.
On each affine chart their coordinate maps j_sigma have formula
 a tensor t tensor b mapping to a tensor sigma(t)b.
The distinguished sheet is j_inclusion under the recorded fibre isomorphism.
For H = geometric Frobenius of Y and g = geometric Frobenius of X, direct evaluation
on these tensors gives j_sigma followed by H = g followed by j_(gamma^-1 sigma).
Induction therefore identifies the range of cyclic sheet i with the component
labelled gamma^-i restricted to E; precomposition by g^i does not change a range.
Every embedding E -> k has image E: it preserves the roots of T^(q^m)-T, which are
exactly E. Thus the finite-field Frobenius bijection enumerates these labels exactly
once for 0 <= i < m. Pulling back the disjoint covering consequently gives both
assertions. The idempotents used to identify the components come from the constant
factor, so the affine descriptions agree on overlaps. If X_0 is empty both assertions
hold for empty ranges; if m=1 there is one component and disjointness is vacuous. -/
theorem constantExtensionCyclicSheetPartition :
    Pairwise (fun i j : Fin m ↦ Disjoint
      (Set.range (constantExtensionCyclicSheet D m hm X₀ i))
      (Set.range (constantExtensionCyclicSheet D m hm X₀ j))) ∧
    (⋃ i : Fin m, Set.range (constantExtensionCyclicSheet D m hm X₀ i)) = Set.univ := by sorry

end WeilConjectures
