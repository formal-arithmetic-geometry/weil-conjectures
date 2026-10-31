/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointFieldTensorRationalDescentData

/-! # Common-stage part of point-field tensor descent

This is the common finite-field and algebraically closed coefficient subproblem.
(blueprint: lem-sf-point-field-tensor-descent-qbar-helper).
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

/-- Common-stage data extending a fixed rational family to Ω.
(blueprint: lem-sf-point-field-tensor-descent-qbar-helper).

Proof source: the common-field paragraph of the proof of
`lem-sf-point-field-tensor-descent`.  Represent finitely many inputs over one finite
coefficient field, transport by the scalar square, and use the resulting coherent
formula in the filtered Hom colimit. -/
structure PointFieldTensorQbarDescentData
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E)
    (R : PointFieldTensorRationalDescentData D l hl I) where
  qbar : PointFibreDerivedTensorComparisonData (𝟭 _)
    (pointQbarFibre D l hl Ω ⋙ DerivedCategory.pointFdQbarRealization l Ω)
    (pointQbarSourceTensor D l hl Ω)
    (⟨Padic.finiteCoefficientBase l Ω, (R.rational
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω))).monoidal.tensorUnit⟩)
    (pointModuleDerivedBraiding Ω)
  stage_scalar : ∀ L : Padic.FiniteCoefficientFields l Ω,
    PointModuleScalarTensorData (pointTensorStageEmbedding l Ω L)
      (DerivedCategory.fieldDerivedScalarExtension (pointTensorStageEmbedding l Ω L))
  stage_scalar_counit : ∀ L : Padic.FiniteCoefficientFields l Ω,
    (stage_scalar L).counit =
      (ModuleCat.extendScalars.{u, u, u}
        (pointTensorStageEmbedding l Ω L)).mapDerivedCategoryFactors.hom
  qbar_model : ∀ F : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (n : ℕ), PointFiniteTensorData D l E n,
    PointQbarTensorCanonical D l hl Ω
      { finite := F, integral := I, rational := R.rational, qbar := qbar } stage_scalar
  qbar_unit : ∀ F : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] (n : ℕ), PointFiniteTensorData D l E n,
    PointQbarTensorUnitCanonical D l hl Ω
      { finite := F, integral := I, rational := R.rational, qbar := qbar }
      (stage_scalar (Padic.finiteCoefficientBase l Ω))

/-- A rational package has a coherent common-stage extension.
Source: Stacks 07A4 and the recorded common-stage coefficient construction
(blueprint: lem-sf-point-field-tensor-descent-qbar-helper).

Proof: for each finite stage `L` take the canonical derived scalar extension along
`L → Ω` with its universal counit and balanced tensorator. Represent two inputs at a
common finite stage `L` above their compositum and extend the rational comparison
`R.rational L` to Ω through this tensorator. The rational scalar squares
`R.rational_scalar`, whose field-scalar tensorators are canonical by their counits,
identify the formulas after every larger-stage transport `L ≤ L'`, so they define one
natural comparison on the Hom colimits. The associator, Koszul symmetry and unit
equations are checked at one common finite stage, where they are the rational
equations; the same calculation gives the formula at every common stage and the
prescribed base-stage unit. Finite-level data do not enter, so the formulas hold for
every finite family `F`. -/
theorem pointFieldTensorQbarDescent
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (I : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E], PointIntegralTensorData D l hl E)
    (R : PointFieldTensorRationalDescentData D l hl I) :
    Nonempty (PointFieldTensorQbarDescentData D l hl Ω I R) := by
  sorry

end WeilConjectures
