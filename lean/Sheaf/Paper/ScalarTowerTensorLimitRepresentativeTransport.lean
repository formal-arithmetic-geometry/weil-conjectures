/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G8
-/
module

public import Sheaf.Paper.ScalarTowerTensorLimitStrictWitness

/-! # Good representative transport

The strict K-flat calculation is isolated from the later localization and
completed-limit assembly.
(blueprint: stage3-pur-scalar-tensor-limit-good-representatives)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible]
  integralCompletedTensor scalarReduction tensorReduction
  integralComparisonDerivedSequenceScalar

/--
The strict K-flat calculation gives the displayed map equality after passing
from good cochain representatives to the derived quotient.  This is the
localization input for the limit transport below; it has no arbitrary
constructible inputs and no completed-tensor comparison.
Source: Stacks 07A4 and 0941 (blueprint:
stage3-pur-scalar-tensor-limit-good-representatives).
-/
theorem scalarTowerTensorLimitSquare_on_good_representatives (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (_hstrict : DerivedSigmaModel l E L ι W SE SL α) :
    ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
      (β : (integralScalarExtensionOfUniverses l E L ι W).obj
          ((integralCompletedTensor l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ⟶
        (integralCompletedTensor l L W).obj
          ((integralScalarExtension l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj P),
            (integralScalarExtension l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj Q))),
      β ≫ TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj P),
            (integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj P))
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj Q)))) =
      SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
            (tensorReduction l E W SE ρE TE
              ((integralOperationsGoodLocalization l E W).obj P)
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
          α.hom.app
            (SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj P),
              SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj Q))) := by
  sorry

end WeilConjectures.ScalarExtensionTower
