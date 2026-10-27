/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorCompatibility

/-! # Scalar compatibility of the integral point tensor augmentation

Source: Stacks 07A4, 0941 and 031B.
(blueprint: lem-sf-point-integral-tensor-scalar-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Normalized completion maps commute with the specified scalar tensor chain.
Source: Stacks 07A4 and 0941, integral point comparison proof step 2
(blueprint: lem-sf-point-integral-tensor-scalar-compatibility).

Proof: evaluate both sides in each finite quotient first coordinate. The defining
normalization of scalarTensorTower and scalarTensorLevel sends the scalar-extended
quotient tensor generator to the quotient tensor of the extended entries. Balance
moves the two scalar coefficients to their product a*b, giving equality there.
In the shifted coordinate both sides vanish: the source completion has zero
shifted coordinate and the diagonal scalarRoosMap and integralOperationsRoosMap
preserve that coordinate, including the product projection. The product projections
are jointly monic after sections, since section evaluation and scalar restriction
preserve products. Finally the two biproduct coordinates of mappingCocone are
jointly monic, so the two displayed sections agree. This is an identity of actual
chain representatives, independent of the derived monoidal data. -/
theorem pointIntegralTensorScalarCompatibility
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L)
    (I₁ : PointIntegralTensorData D l hl E) (I₂ : PointIntegralTensorData D l hl L)
    (C₁ : PointIntegralTensorCanonical D l hl E I₁)
    (C₂ : PointIntegralTensorCanonical D l hl L I₂) :
    PointIntegralTensorScalarSquare D l hl E L ι I₁ I₂ C₁ C₂ := by
  sorry

end WeilConjectures
