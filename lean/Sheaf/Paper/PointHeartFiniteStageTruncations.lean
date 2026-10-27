/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.Paper.PointHeartFiniteStageData

/-! # A step of the exact point-heart and finite-stage argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The rational and common-stage ambient point realizations admit canonical
truncation comparisons, and the rational comparisons commute with scalar extension.
Source: BBD 1.3.3; steps 1--2 and 4 of lem-zl-point-heart-finite-stage
(blueprint: lem-zl-point-heart-truncation-squares).

Proof: sections and rational localization are exact and commute with cohomology,
so the rational ambient realization is t-exact. The common-stage standard classes
are the isomorphism closures of finite-stage standard classes, so its realization
is t-exact too. Apply the t-exact truncation comparison for each sign and each
integer, obtaining precisely its counit and unit equations. Scalar extension is
also t-exact by constructible truncation stability and exact tensor extension of
fields. Apply the same comparison to source and target scalar extension. Both
routes around either square have the same composite with the truncation counit,
or the same precomposition with its unit, by naturality of the specified sections
scalar comparison. The truncation universal property identifies them. This gives
simultaneously the family c, its scalar squares and the common-stage comparisons;
identity extensions and zero objects obey the same universal properties. -/
theorem zl_point_heart_truncation_squares :
    (∃ c : ∀ (E' : Type u) [Field E'] [Algebra (Padic l) E']
        [FiniteDimensional (Padic l) E'],
        ZlPointTruncationComparison E' (zlPointT D l hl E') (zlPointAmbient D l hl E'),
      (∀ (E' L' : Type u) [Field E'] [Algebra (Padic l) E']
        [FiniteDimensional (Padic l) E'] [Field L'] [Algebra (Padic l) L']
        [FiniteDimensional (Padic l) L'] (i : E' →ₐ[Padic l] L'),
        ZlPointScalarTruncationSquare D l hl E' L' i (c E') (c L'))) ∧
    Nonempty (ZlPointTruncationComparison Ω
      (sfCommonStageStandardTStructure l (Spec (.of D.k)) Ω D hl)
      (zlPointCommonAmbient D l hl Ω)) := by sorry

end WeilConjectures
