/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorQbar
public import Sheaf.Paper.PointFibreDerivedTensorCompatibility
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

Proof: integral constructibility implies the finite-Tor condition by the integral
residue-Tor theorem. Extend the normalized integral comparison and its coefficient
unit through rationalization. The balanced scalar tensorator and the recorded
coefficient/carrier lift give the rational tensor and unit formulas. Faithfulness
of the lift fixes the small comparison uniquely. The integral scalar square gives
the rational scalar square after localization. Apply common-field descent: represent
two inputs at a common finite field and extend their rational comparison to the
closed coefficient field. The scalar square identifies the formulas after every
larger-field transport, so they define a natural comparison on the Hom colimits.
The associator, Koszul symmetry and unit equations can all be checked at one common
finite field, where they are the rational equations. The same calculation gives
the formula at every common field and the prescribed base-stage unit. All target
scalar functors have their universal counits, and their balanced tensorators on
arbitrary representatives, from derived scalar extension. Finite-level data do not
enter either field-stage formula. -/
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
  sorry

end WeilConjectures
