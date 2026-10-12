/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleRestrictedTotalResolution

/-! # Augmentation and inclusion of the restricted total

Source: Stacks Project, Tags 015J and 0133, restricted augmented total.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Totalization of the column inclusion before applying global sections.
Source: Stacks Project, Tag 015J, proof remark (3).
(blueprint: lem-weil-pbc-etale-restricted-augmentation-inclusion). -/
noncomputable def etaleRestrictedTotalInclusion
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :=
  HomologicalComplex₂.total.map
    ((HomologicalComplex₂.flipFunctor
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        ((CartanEilenbergPresentation.mappedFunctor
          (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))).map
            (T.I.ιStupidTrunc (ComplexShape.embeddingUpIntGE q)))) (ComplexShape.up ℤ)

/-- The restricted augmentation commutes with the two truncation inclusions.
Source: Stacks Project, Tag 015J, proof remark (3), and Tag 0133.

Proof: Evaluate in total degree n and use the formula for a totalized map on
its degree-zero resolution summand. Naturality of extension by zero transports
that summand to the degree-zero summand of the full total. If n ≥ q, the
stupid-truncation projection followed by its inclusion is the identity on
T.I.X n. Cancel this pair in etaleRestrictedAugmentationComponent and apply
T.aug_formula. If n < q, the source term of the truncated K is zero, so the
two maps are equal. Chain-map extensionality now proves the equation. The
calculation has no positivity condition on q, and also covers the zero complex
and empty diagonals.
(blueprint: lem-weil-pbc-etale-restricted-augmentation-inclusion). -/
theorem etaleRestrictedAugmentation_inclusion
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    etaleRestrictedAugmentation X K T q ≫ etaleRestrictedTotalInclusion X K T q =
      K.obj.ιStupidTrunc (ComplexShape.embeddingUpIntGE q) ≫ T.aug := by sorry

end AlgebraicGeometry.Etale
