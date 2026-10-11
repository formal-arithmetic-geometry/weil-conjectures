/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction

/-!
# Unrestricted strict-henselization stalk formula

Source: Stacks Project, Theorem 59.53.1, Tag 03Q9, first assertion
(blueprint: lem-weil-pbc-unrestricted-strict-henselization-stalk).
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- For every abelian étale sheaf, the canonical strict-local restriction is an isomorphism.
The germ map `r` is specified by its neighbourhood components; its existence and uniqueness
are supplied by `existsUnique_strictHenselizationStalkRestriction`. The canonical map is
`r ≫ strictHenselizationCohomologyComparison`, with target the cohomology of the inverse
image along the first projection of the strict-local base change.
Source: Stacks Project, Tag 03Q9, first assertion and proof
(blueprint: lem-weil-pbc-unrestricted-strict-henselization-stalk).

Proof:
1. By `sbc-lem-higher-direct-image-presheaf`, the higher direct image is the sheafification
of the cohomology presheaf. By `lem-weil-pbc-sheafification-geometric-stalk`, its stalk is
the filtered colimit of neighbourhood cohomology groups.
2. By `lemma-weil-pbc-affine-neighbourhood-cofinal`, restrict to affine pointed
neighbourhoods. Their limit is the strict henselization
(`def-weil-pbc-strict-henselization-limit`), and fibre products commute with this limit
(`lemma-weil-pbc-fibre-product-limit`). Quasi-compactness and quasi-separatedness of `f`
give qcqs base changes, and the transition maps are affine.
3. Fix one affine pointed neighbourhood and restrict to the cofinal system over it.
Apply `lem-weil-pbc-derived-etale-cohomology-limit` to the restricted sheaf in degree zero.
Exact inverse image keeps it in degree zero (`def-weil-pbc-derived-inverse-image`), and
inverse images compose (`lem-weil-pbc-inverse-image-composition`). Its degree-q cohomology
is the sheaf cohomology (`def-weil-pbc-etale-cohomology`). The continuity isomorphism is
induced by restriction along the projections, so its composite with the stalk-colimit
identification is precisely the canonical restriction in the statement. -/
theorem unrestricted_strictHenselization_stalk
    {X S : Scheme.{w}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω]
    (xbar : Spec (.of Ω) ⟶ S)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w + 1}) (q : ℕ) :
    ∃ r : (Scheme.pointSmallEtale xbar).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{w + 1} f).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ⟶
        (Sheaf.Γ (Scheme.strictHenselizationScheme xbar).smallEtaleTopology
          AddCommGrpCat.{w + 1}).obj
          ((upperStar AddCommGrpCat.{w + 1} (Scheme.strictHenselizationStructuralMap xbar)).obj
            ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
              ((rightDerivedLowerStarPlus AddCommGrpCat.{w + 1} f).obj
                ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))),
      IsStrictHenselizationStalkRestriction xbar
          ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{w + 1} f).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) r ∧
        IsIso (r ≫ strictHenselizationCohomologyComparison xbar f F q) := by
  sorry

end AlgebraicGeometry.Etale
