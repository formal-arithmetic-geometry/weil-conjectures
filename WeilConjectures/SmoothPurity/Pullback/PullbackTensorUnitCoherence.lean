/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorIntegralUnitCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorRationalUnitCoherence
import WeilConjectures.SmoothPurity.Pullback.PullbackTensorCommonStageUnitCoherence

/-! # Units of the higher pullback tensor comparisons

## Implementation details

At the whole-system level inverse image sends the coefficient-ring unit to the coefficient-ring
unit, and the multiplication maps on pure tensors give both unit equations. The reconstruction
counit identifies the integral units and unitors with these system units and unitors; the
system unit comparison is lifted along fully faithful coherent reduction, and uniqueness follows
by cancelling the invertible comparison and unitor. The integral comparison is then localized
to give the rational statement, and the common-stage statement is obtained by representing the
units at a finite field via the scalar unit comparison.

## References

* [Stacks Project, Tags 03EL, 07A4 and 0941]
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

/-- The prescribed higher tensor comparisons preserve the normalized tensor units. -/
theorem pullbackTensorUnitCoherence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    canonicalIntegralPullbackTensor_unit l E f ∧
      canonicalRationalPullbackTensor_unit l E f ∧
        canonicalCommonStagePullbackTensor_unit l Ω f := by
  exact ⟨pullbackTensorIntegralUnitCoherence l E f,
    pullbackTensorRationalUnitCoherence l E f,
    pullbackTensorCommonStageUnitCoherence l Ω f⟩

end WeilConjectures
