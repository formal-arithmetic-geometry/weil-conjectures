/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensorQbar
public import WeilConjectures.AlgebraicGeometry.PointFibreDerivedTensorCompatibility
import WeilConjectures.AlgebraicGeometry.PointFieldTensorQbarDescentData
/-! # Point tensor comparisons after localization and common-field descent

Source: blueprint rational and algebraically closed coefficient constructions.
(blueprint: lem-sf-point-field-tensor-descent).
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

/-- The field-stage comparisons, with no finite-level or integral-stage
construction included in the data.
Source: blueprint orders 1509 and 1826
(blueprint: lem-sf-point-field-tensor-descent). -/
structure PointFieldTensorComparison
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E) where
  /-- The rational tensor comparison at each finite coefficient field. -/
  rational : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorData D l hl E (I E)
  /-- The common-stage comparison, with the prescribed base-field unit. -/
  qbar : PointFibreDerivedTensorComparisonData (𝟭 _)
    (pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω)
    (pointQbarSourceTensor D l hl Ω)
    (⟨Padic.finiteCoefficientBase l Ω, (rational
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω))).monoidal.tensorUnit⟩)
    (pointModuleDerivedBraiding Ω)
  /-- The actual coefficient/carrier lift, with its pure-tensor normalization. -/
  lift : ∀ (E : Type u) [Field E], PointFibreLiftTensorData E
  /-- Canonical derived fraction-field tensor. -/
  localization : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointModuleScalarTensorData (pointIntegralToField l E)
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).mapDerivedCategory
  /-- Its counit is the recorded exact-functor localization comparison. -/
  localization_counit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], (localization E).counit =
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategoryFactors.hom
  /-- Rational comparison is precisely the localized integral comparison. -/
  rational_model : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorCanonical D l hl E
      (I E) (rational E) (lift E) (localization E)
  /-- Rational units are obtained from the same normalized integral units. -/
  rational_unit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E], PointRationalTensorUnitCanonical D l hl E
      (I E) (rational E) (lift E) (localization E)
  /-- Canonical derived field-extension tensorators. -/
  field_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    PointModuleScalarTensorData ι.toRingHom
      (DerivedCategory.fieldDerivedScalarExtension ι.toRingHom)
  /-- Counits are the fixed comparisons of the exact coefficient functors. -/
  field_scalar_counit : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    (field_scalar E L ι).counit =
      (ModuleCat.extendScalars.{u, u, u} ι.toRingHom).mapDerivedCategoryFactors.hom
  /-- The rational cross-field square uses the recorded scalar comparison. -/
  rational_scalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
    PointRationalTensorScalarSquare D l hl E L ι (I E) (I L)
      (rational E) (rational L) (field_scalar E L ι)
  /-- Tensorator for extending any finite coefficient stage to Ω. -/
  stage_scalar : ∀ L : Padic.FiniteCoefficientFields l Ω,
    PointModuleScalarTensorData (pointTensorStageEmbedding l Ω L)
      (DerivedCategory.fieldDerivedScalarExtension (pointTensorStageEmbedding l Ω L))
  /-- The stage scalar counit is also the specified exact-functor comparison. -/
  stage_scalar_counit : ∀ L : Padic.FiniteCoefficientFields l Ω,
    (stage_scalar L).counit =
      (ModuleCat.extendScalars.{u, u, u}
        (pointTensorStageEmbedding l Ω L)).mapDerivedCategoryFactors.hom
  /-- The closed coefficient comparison is canonical at every common finite stage. -/
  qbar_model : ∀ F : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (n : ℕ), PointFiniteTensorData D l E n,
    PointQbarTensorCanonical D l hl Ω
      { finite := F, integral := I, rational := rational, qbar := qbar } stage_scalar
  /-- Its unit is the scalar extension of the actual rational coefficient unit. -/
  qbar_unit : ∀ F : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (n : ℕ), PointFiniteTensorData D l E n,
    PointQbarTensorUnitCanonical D l hl Ω
      { finite := F, integral := I, rational := rational, qbar := qbar }
    (stage_scalar (Padic.finiteCoefficientBase l Ω))

/-- Normalized integral comparisons descend to the actual rational and common-field
coefficient constructions.
Source: blueprint orders 1509 and 1826
(blueprint: lem-sf-point-field-tensor-descent).

Proof: the rationalization part (rational comparisons, coefficient/carrier lifts,
localization and field-scalar tensorators with their counits, rational models, units and
scalar squares) is `pointFieldTensorRationalDescent`; given that rational package, the
common-stage part (the comparison over Ω, the stage tensorators with their counits and
the common-stage model and unit formulas) is `pointFieldTensorQbarDescent`. The
structure `PointFieldTensorComparison` consists exactly of the fields of these two
packages, which are combined field by field. -/
theorem pointFieldTensorDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E)
    (C : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorCanonical D l hl E (I E))
    (hscalar : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (L : Type u) [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L),
      PointIntegralTensorScalarSquare D l hl E L ι (I E) (I L) (C E) (C L)) :
    Nonempty (PointFieldTensorComparison D l hl Ω I) := by
  obtain ⟨R⟩ := pointFieldTensorRationalDescent D l hl I C hscalar
  obtain ⟨Q⟩ := pointFieldTensorQbarDescent D l hl Ω I R
  exact ⟨{
    rational := R.rational
    qbar := Q.qbar
    lift := R.lift
    localization := R.localization
    localization_counit := R.localization_counit
    rational_model := R.rational_model
    rational_unit := R.rational_unit
    field_scalar := R.field_scalar
    field_scalar_counit := R.field_scalar_counit
    rational_scalar := R.rational_scalar
    stage_scalar := Q.stage_scalar
    stage_scalar_counit := Q.stage_scalar_counit
    qbar_model := Q.qbar_model
    qbar_unit := Q.qbar_unit }⟩

end WeilConjectures
