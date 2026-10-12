/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleRestrictedAugmentationInclusion

/-! # Global sections of the restricted resolution comparison

Source: Stacks Project, Tag 015J, finite-diagonal mapped-total comparison.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The complex map obtained by sections of the restricted resolution comparison
is the prescribed sections inclusion followed by the full comparison.
Source: Stacks Project, Tag 015J, proof remark (3).

Proof: In degree n, precompose both maps with the images under Γ of the
restricted total summands in bidegrees (r,s), where r ≥ 0, s ≥ q, r+s=n.
The finite-diagonal coproduct comparison etaleCEMappedTotalIso identifies
these generators with the summands of the restricted mapped total. The total
map sends each summand through the corresponding column inclusion to the
full total. Apply T.w_formula to that full summand. Naturality of the
extension-by-zero comparison cancels the extension isomorphisms on both
sides, leaving Γ of the sheaf-total inclusion followed by T.comparison.
The coproduct universal property gives equality in degree n, and chain-map
extensionality gives the assertion. Negative resolution degrees and omitted
columns are zero. Empty diagonals and zero terms require no separate choice;
the same proof applies to every integer q.
(blueprint: lem-weil-pbc-etale-restricted-sections-comparison-map). -/
theorem etaleRestrictedSections_comparison_map
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (etaleRestrictedTotalInclusion X K T q ≫ T.comparison) =
      etaleRestrictedSectionsInclusion X K T q ≫ T.w := by sorry

end AlgebraicGeometry.Etale
