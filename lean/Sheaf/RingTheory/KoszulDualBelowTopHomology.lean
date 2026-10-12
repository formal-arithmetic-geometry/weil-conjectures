/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.RingTheory.KoszulDualComplex
public import Sheaf.RingTheory.KoszulRegularSequence

/-!
# Dual Koszul cohomology below the top degree

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, complementary contraction.
(blueprint: lem-sc-koszul-dual-below-top-homology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ExteriorAlgebra

/-- The signed dual of a Koszul-regular complex has zero cohomology below its top degree.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, the complementary
contraction isomorphism of complexes up to signs.
(blueprint: lem-sc-koszul-dual-below-top-homology).

Proof: Put E = A^r with its ordered standard basis. The dual of an ordered wedge
of n basis vectors maps to the complementary wedge of r-n vectors, multiplied by
the permutation sign. These maps are linear isomorphisms for 0 <= n <= r.
The contraction formula on a basis wedge shows that signed precomposition with
contraction corresponds to contraction on the complementary wedge up to a sign
that depends only on n and r. Choose the degree-zero sign to be 1 and recursively
multiply the degree-n isomorphism by the unit sign needed for the next square to
commute. Thus the resulting reversed finite Koszul complex and the signed dual
have isomorphic cohomology in degree n. For n < r this is the homology of the
original Koszul complex in the positive degree r-n, which is zero by the given
Koszul-regularity. The boundary degree n=0 uses the zero term beyond degree r
in the original complex; its exterior power is zero because E has r basis vectors.
For r=0 there is no n < r. The argument also works over the zero ring. -/
theorem koszulDual_isZero_homology_below_top
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (n : ℕ) (hn : n < r) :
    IsZero ((koszulDualComplex A r f).homology n) := by sorry

end ExteriorAlgebra
