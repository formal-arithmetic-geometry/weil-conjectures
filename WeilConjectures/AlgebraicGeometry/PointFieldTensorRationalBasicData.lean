/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensorQbar
public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensorCompatibility

/-! # Basic rational point-field tensor descent data

This interface isolates the construction of the coefficient/carrier lifts and of the
localization and finite field scalar-extension tensorators, each pinned by its universal
counit and balanced representative model, from the rational tensor comparison and its
normalization equations.
(blueprint: lem-sf-point-field-tensor-descent-rational-basic)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

/-- The coefficient/carrier lift and scalar-extension construction data.
(blueprint: lem-sf-point-field-tensor-descent-rational-basic).

The fields are the coefficient/carrier lift, the fraction-field localization tensorator
and the finite field scalar tensorators, together with their universal counits.  Each
field is pinned by its own universal property and balanced representative model.  The
rational tensor comparison is not part of this package: its strong structure is free
data, fixed only by the normalization equations, and is constructed together with them
in `PointFieldTensorRationalCompatibilityData`.
-/
structure PointFieldTensorRationalBasicData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E) where
  lift : ∀ (E : Type u) [Field E], PointFibreLiftTensorData E
  localization : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointModuleScalarTensorData (pointIntegralToField l E)
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory
  localization_counit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], (localization E).counit =
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategoryFactors.hom
  field_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    PointModuleScalarTensorData ι.toRingHom
      (DerivedCategory.fieldDerivedScalarExtension ι.toRingHom)
  field_scalar_counit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    (field_scalar E L ι).counit =
      (ModuleCat.extendScalars.{u, u, u} ι.toRingHom).mapDerivedCategoryFactors.hom

/-- The lift and scalar-extension construction exists.
(blueprint: lem-sf-point-field-tensor-descent-rational-basic).

Proof source: the rationalization paragraph of the proof of
`lem-sf-point-field-tensor-descent`.  Take the exact fraction-field extension
`O_E → E` and, for every finite extension `ι : E → L`, the exact finite-field
extension, each with its canonical derived counit; these are left derived functors of
exact functors, so the counit has the universal property.  Their strong monoidal
structures are the balanced tensorators `a ⊗ (x ⊗ y) ↦ (a ⊗ x) ⊗ (1 ⊗ y)` on
K-flat representatives, extended by naturality (Stacks 06YS, 06Y6, 07A4).  The
coefficient/carrier universe lift is exact and fully faithful; its tensorator is
`up (x ⊗ y) ↦ up x ⊗ up y` on representatives.
-/
theorem pointFieldTensorRationalBasic
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E) :
    Nonempty (PointFieldTensorRationalBasicData D l hl I) := by
  sorry

end WeilConjectures
