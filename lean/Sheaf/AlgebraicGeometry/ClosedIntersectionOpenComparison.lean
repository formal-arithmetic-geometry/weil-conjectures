/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.ClosedIntersectionAugmentedRow

/-! Unit-normalized open compatibility for the augmented intersection row. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ClosedIntersection

/-- Open restriction carries any augmented intersection row to a row for the
base-changed family, preserving all units, faces, and summand projections.

Source: Stacks Project, Tags 09AA, 09BN and 00XZ; step 3 of
lem-sfb-closed-intersection-vertex-contraction.
(blueprint: lem-sfb-closed-intersection-open-comparison).

Proof: Localize the pro-etale site at the open scheme. On a test object T over
that open, both open restriction of a closed direct image and direct image of the
restricted sheaf evaluate on T times_X the closed subscheme. The resulting
sectionwise isomorphism is linear and natural. For inverse images use the
unit-normalized composition comparison around the pullback square. The ring
comparison is its specified ringComp comparison, and the module comparison sends
the successive inverse-image unit sections to the unit section transported by
the canonical pasting isomorphism. These give delta, normalized and beta of
BaseChange. Transposing beta by the fixed closed adjunction gives delta followed
by the closed counit, because its defining section map is that evaluation map;
this proves mate.
The pullbacks of finite products over X are the finite products over the new
base. For the empty index use the pullback of Z instead. These identifications
give comparison for every term, preserving the actual unit sections. Closed
units are epimorphisms by 09AH; thus the unit equation uniquely determines each
inclusion face, and the comparison preserves it. Non-inclusion faces are zero.
For a nonempty family construct the new row from the signed-refinement theorem
and the augmented-row bridge, using the base-changed hypotheses. For an empty
family take E_Z in degree -1 and zero in all other degrees, with zero differential.
Take finite products of the comparisons above. Pullback preserves these finite
products, and comparison of the signed matrices gives a map of complexes and
its inverse. Equivalently construct the base row from the same unit faces on
the new base and use the product comparisons for its differentials. This gives
rowIso, and composition with each product projection is exactly components.
All constructions include degree -1 and empty products. No quasi-compactness of
the open immersion, affine hypothesis, or covering hypothesis is used. -/
theorem closed_intersection_open_comparison {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] {m : ℕ} (W : Fin m → Over X)
    (hclosed : ∀ a, IsClosedImmersion (W a).hom)
    (hfactor : ∀ a, Nonempty (W a ⟶ Over.mk i))
    (hqc : ∃ U : X.Opens, Set.range U.ι = (Set.range i)ᶜ ∧ QuasiCompact U.ι)
    (hqcW : ∀ a, ∃ U : X.Opens,
      Set.range U.ι = (Set.range (W a).hom)ᶜ ∧ QuasiCompact U.ι)
    (A : Rings X) (D : Row i W A)
    {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    ∃ D' : Row (pullback.fst g i) (finiteClosedPullbackFamily W g) (inverseRing g A),
      Nonempty (OpenCompatibility D g D') := by sorry

end AlgebraicGeometry.ClosedIntersection
