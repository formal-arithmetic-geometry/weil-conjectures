/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensorQbar
public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensorCompatibility
import WeilConjectures.AlgebraicGeometry.PointFieldTensorRationalCompatibilityData

/-! # Rational part of point-field tensor descent

This is the rationalization and field-scalar subproblem extracted from
`pointFieldTensorDescent`.
(blueprint: lem-sf-point-field-tensor-descent-rational-helper).
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

/-- All rational and field-scalar data required by the point-field comparison.
(blueprint: lem-sf-point-field-tensor-descent-rational-helper).

Proof source: the rationalization paragraph of the proof of
`lem-sf-point-field-tensor-descent`.  Integral tensor models are localized through
the balanced scalar tensorator; the coefficient/carrier lift is normalized on pure
tensors; and the integral scalar square descends through localization. -/
structure PointFieldTensorRationalDescentData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E) where
  rational : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorData D l hl E (I E)
  lift : ∀ (E : Type u) [Field E], PointFibreLiftTensorData E
  localization : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointModuleScalarTensorData (pointIntegralToField l E)
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory
  localization_counit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], (localization E).counit =
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategoryFactors.hom
  rational_model : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorCanonical D l hl E
      (I E) (rational E) (lift E) (localization E)
  rational_unit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorUnitCanonical D l hl E
      (I E) (rational E) (lift E) (localization E)
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
  rational_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    PointRationalTensorScalarSquare D l hl E L ι (I E) (I L)
      (rational E) (rational L) (field_scalar E L ι)

/-- Integral models and scalar squares produce the rational descent package.
Source: Stacks 07A4 and the recorded coefficient constructions
(blueprint: lem-sf-point-field-tensor-descent-rational-helper).

Proof: integral constructibility implies the finite-Tor condition by the integral
residue-Tor theorem (`lem-coef-integral-residue-tor`). Take the canonical derived
fraction-field extension `O_E → E` with its universal counit; its balanced tensorator on
representatives is the localization tensorator. Extend the normalized integral
comparison `C E` and its coefficient unit through it; with the recorded
coefficient/carrier lift, normalized on pure tensors, this gives the rational tensor
and unit formulas, and faithfulness of the lift fixes the small rational comparison
uniquely. For a finite extension `ι : E → L` take the canonical derived field-scalar
extension with its universal counit and balanced tensorator; localizing the integral
scalar square `hscalar E L ι` gives the rational scalar square. -/
theorem pointFieldTensorRationalDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E)
    (C : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorCanonical D l hl E (I E))
    (hscalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
      PointIntegralTensorScalarSquare D l hl E L ι (I E) (I L) (C E) (C L)) :
    Nonempty (PointFieldTensorRationalDescentData D l hl I) := by
  obtain ⟨B⟩ := pointFieldTensorRationalBasic D l hl I
  obtain ⟨K⟩ := pointFieldTensorRationalCompatibility D l hl I C hscalar B
  exact ⟨{
    rational := K.rational
    lift := B.lift
    localization := B.localization
    localization_counit := B.localization_counit
    rational_model := K.rational_model
    rational_unit := K.rational_unit
    field_scalar := B.field_scalar
    field_scalar_counit := B.field_scalar_counit
    rational_scalar := K.rational_scalar }⟩

end WeilConjectures
