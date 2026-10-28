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

-- STATEMENT-DISPUTED: β is arbitrary, including zero. On complete inputs a canonical
-- isomorphism supplies another β; the universal equation then forces both the fixed
-- coordinate and the entire postcomposition to vanish. See the proved diagnostic below.
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


private theorem forall_bridge_iff_zero
    {C : Type*} [Category C] [HasZeroMorphisms C] {A B D : C}
    (e : A ≅ B) (f : B ⟶ D) (g : A ⟶ D) :
    (∀ β : A ⟶ B, β ≫ f = g) ↔ f = 0 ∧ g = 0 := by
  constructor
  · intro h
    have hg : g = 0 := by simpa only [zero_comp] using (h 0).symm
    refine ⟨?_, hg⟩
    apply (cancel_epi e.hom).1
    simpa only [comp_zero] using (h e.hom).trans hg
  · rintro ⟨rfl, rfl⟩ β
    exact comp_zero

/-- On complete inputs the arbitrary-bridge equation is equivalent to two vanishing
conditions, not to strict scalar/tensor compatibility. This diagnoses the unrestricted
bridge quantifier in `scalarTowerTensorLimitSquare_on_good_representatives`.

Proof: the canonical completed scalar/tensor comparison is an isomorphism between
its two bridge objects. The zero bridge first forces the fixed right-hand coordinate
to vanish. Using the isomorphism as bridge and cancelling it forces the left-hand
postcomposition to vanish. Conversely both zero conditions imply the equation for
any bridge. No representative normalization or strict comparison hypothesis is used.
Source: the displayed equation of this node and the canonical comparison of
`IntegralOperationsScalarComparisons`; elementary zero-morphism identities
(blueprint: stage3-pur-scalar-tensor-limit-good-representatives). -/
private theorem scalarTowerTensorLimitSquare_arbitrary_bridge_iff_zero (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (M N : DerivedCategory (integralTowerModules.{u, u} l E W))
    (hM : IsSfDerivedComplete l E W M) (hN : IsSfDerivedComplete l E W N)
    (hT : IsSfDerivedComplete l E W ((integralCompletedTensor l E W).obj (M, N))) :
    (∀ β : (integralScalarExtensionOfUniverses l E L ι W).obj
        ((integralCompletedTensor l E W).obj (M, N)) ⟶
      (integralCompletedTensor l L W).obj
        ((integralScalarExtension l E L ι W).obj M,
          (integralScalarExtension l E L ι W).obj N),
      β ≫ TL.realization.hom.app
          ((integralScalarExtension l E L ι W).obj M,
            (integralScalarExtension l E L ι W).obj N) ≫
        (coefficientSequenceLimit l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY M)
            (scalarReduction l E L ι W SE SL ρL SY N))) =
      SY.realization.hom.app ((integralCompletedTensor l E W).obj (M, N)) ≫
        (coefficientSequenceLimit l L W).map
          ((integralComparisonDerivedSequenceScalar l E L ι W).map
              (tensorReduction l E W SE ρE TE M N) ≫
            α.hom.app (SE.reduction.obj M, SE.reduction.obj N))) ↔
    (TL.realization.hom.app
        ((integralScalarExtension l E L ι W).obj M,
          (integralScalarExtension l E L ι W).obj N) ≫
      (coefficientSequenceLimit l L W).map
        (SL.systemClosed.tensor.map (Prod.mkHom
          (scalarReduction l E L ι W SE SL ρL SY M)
          (scalarReduction l E L ι W SE SL ρL SY N))) = 0) ∧
    (SY.realization.hom.app ((integralCompletedTensor l E W).obj (M, N)) ≫
      (coefficientSequenceLimit l L W).map
        ((integralComparisonDerivedSequenceScalar l E L ι W).map
            (tensorReduction l E W SE ρE TE M N) ≫
          α.hom.app (SE.reduction.obj M, SE.reduction.obj N)) = 0) := by
  exact forall_bridge_iff_zero (scalarTensorCompleted l E L ι W M N hM hN hT) _ _

end WeilConjectures.ScalarExtensionTower
