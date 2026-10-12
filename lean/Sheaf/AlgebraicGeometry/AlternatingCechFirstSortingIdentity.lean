/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechSortingOperators
public import Mathlib.Algebra.Homology.Homotopy

/-!
# The first Čech sorting identity

Source: Stacks Project, Cohomology of Sheaves, Tag 01FM.
(blueprint: lem-pc-alternating-cech-first-sorting-identity)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The first sorting operator contracts identity minus stable sorting.

Source: Stacks 01FM, equation 20.23.6.1.
(blueprint: lem-pc-alternating-cech-first-sorting-identity)

Proof: The filter selects the unique permutation sorting the pairs (t(k), k)
lexicographically. For each a, its partial-sort filter selects the unique permutation
with the specified prefix and increasing unused original positions. Thus the finite
sum is exactly the junction formula of 20.23.6.1, with no multiplicities.
Expand the two differentials at an arbitrary tuple t. Label every occurrence by its
original position, even when values coincide. Deleting a label j from a sorted tuple
removes that label from its stable sorting permutation and renumbers labels above j.
Do the same in each partial permutation. For a permutation π, deletion of its r-th
position changes its sign by (-1)^(r+π(r)). This follows by moving that position and
its value to the last positions and then restricting the permutation.
Pair a deletion of a nonjunction label in the junction sum with the term in the
junction sum for the corresponding face of t. If the deleted label is in the sorted
prefix the junction number drops by one; if it is in the remaining tail it stays the
same. The deletion-sign formula gives opposite coefficients in the two expansions.
Both transports have the same composites with every projection, hence are equal by
S.universal. The two deletions of the junction label compare consecutive partial
permutations; their terms telescope as a ranges from zero to p. The initial partial
permutation is identity, giving the original cochain with coefficient 1; the final
one is the stable sorting permutation, giving minus its signed pullback. This proves
the identity coordinatewise. In degree zero the incoming differential is zero and
stable sorting is identity. If I is empty every cochain group is a zero object. -/
theorem cechFirstSortingIdentity (X : Scheme.{u}) {I : Type v} [LinearOrder I]
    (U : I → X.Opens) (F : X.Opensᵒᵖ ⥤ AddCommGrpCat.{w})
    (S : SiteCechComplex U (fun i ↦ homOfLE (le_top : U i ≤ ⊤))) (p : ℕ) :
    (Homotopy.nullHomotopicMap' (cechFirstSortingFamily X U F S)).f p =
      𝟙 (S.cochains F p) - cechStableSortingMap X U F S p := by sorry

end AlgebraicGeometry.Scheme
