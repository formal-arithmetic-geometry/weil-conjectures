/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralCompositionCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorRationalCompositionCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageCompositionCoherence

/-! # Composition of the higher pullback tensor comparisons

## References

* Stacks Project, Tags 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

-- Cache the existing category instances while comparing finite-stage arrows.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear sfIntegralConstructible
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

attribute [local irreducible] Scheme.residueField Padic
  canonicalIntegralPullbackTensor_composition canonicalRationalPullbackTensor_composition
  canonicalCommonStagePullbackTensor_composition canonicalIntegralPullbackTensor_unit
  canonicalRationalPullbackTensor_unit canonicalCommonStagePullbackTensor_unit

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- Pullback composition preserves the prescribed tensor comparison at all higher levels. -/
theorem pullbackTensorCompositionCoherence {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    (∀ M N : sfIntegralConstructibleCategory l E Y,
      canonicalIntegralPullbackTensor_composition l E f h M N) ∧
    (∀ M N : sfRationalConstructibleCategory l E Y,
      canonicalRationalPullbackTensor_composition l E f h M N) ∧
    (∀ M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      canonicalCommonStagePullbackTensor_composition l Ω f h M N) := by
  refine ⟨?_, ?_, ?_⟩
  · exact pullbackTensorIntegralCompositionCoherence l E f h
  · exact pullbackTensorRationalCompositionCoherence l E f h
  · exact pullbackTensorCommonStageCompositionCoherence l Ω f h

end WeilConjectures
