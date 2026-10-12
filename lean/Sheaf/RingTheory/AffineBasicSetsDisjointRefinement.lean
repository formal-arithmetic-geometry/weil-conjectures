/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
import Sheaf.RingTheory.AffineBasicSetDifference

/-!
# Disjoint refinement of basic constructible subsets of an affine spectrum

Source: Stacks Project, Algebra, Lemma 10.29.3 (Tag 0G1P), and the refinement step
in Étale Cohomology, Lemma 59.72.1 (Tag 03S0) (blueprint:
lem-weil-pbc-affine-basic-sets-disjoint-refinement).
-/

@[expose] public section

universe u

open Set

namespace PrimeSpectrum

/-- (blueprint: lem-weil-pbc-affine-basic-sets-disjoint-refinement)
For a commutative ring, every finite family of basic constructible subsets of its
prime spectrum has a finite pairwise-disjoint refinement by basic constructible subsets
with the same union.  `BasicConstructibleSetData.toSet` represents
`D(f) ∩ V(g₁, ..., gₙ)` as `V(g₁, ..., gₙ) \ V(f)`.

Source: Stacks Project, Algebra, Lemma 10.29.3 (Tag 0G1P), and the refinement step
in Étale Cohomology, Lemma 59.72.1 (Tag 03S0).

Proof:
1. Induct on the number of input sets, starting with the empty output family.
   Given a disjoint basic family covering the first t input sets, start with the
   singleton family consisting of the next input set. Subtract each old piece in
   turn, replacing each current piece by the finite disjoint basic decomposition
   of its difference supplied by `lem-weil-pbc-affine-basic-set-difference`.
   Pieces arising from different current pieces stay disjoint because they are
   subsets of those pieces. The resulting family covers exactly the next input
   set minus the union of the old family.
2. Keep the entire old family and append the new pieces. Each new piece is
   disjoint from every old piece, so the combined family is finite and pairwise
   disjoint. Its union is the old union together with the next input set.
   After m steps this is the required union; for m = 0 the family is empty. -/
theorem finite_disjoint_basic_constructible_refinement {A : Type u} [CommRing A]
    (m : ℕ) (B : Fin m → BasicConstructibleSetData A) :
    ∃ (p : ℕ) (C : Fin p → BasicConstructibleSetData A),
      (Pairwise fun i j => Disjoint ((C i).toSet) ((C j).toSet)) ∧
      (⋃ i, (B i).toSet) = ⋃ j, (C j).toSet := by
  sorry

end PrimeSpectrum
