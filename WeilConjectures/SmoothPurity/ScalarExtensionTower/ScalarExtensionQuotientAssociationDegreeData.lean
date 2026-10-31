/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels

/-! # Degreewise strict association data

This is the finite balanced-tensor and transition part of the strict quotient
association.  The complex assembly is proved by the parent module.
(blueprint: stage3-pur-scalar-quotient-association-degree-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.coefficientSequenceEssentiallySmall
attribute [local irreducible] WeilConjectures.integralComparisonSequenceScalarModel
universe u
open CategoryTheory Opposite AlgebraicGeometry
namespace WeilConjectures.ScalarExtensionTower

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Degreewise normalized association datum for fixed strict quotient representatives.

Source: Stacks Tags 03EL and 07A4; the finite balanced tensor association and its
successor compatibility.  The finite association is evaluated through the two
`directEvaluation` isomorphisms, and the resulting maps are compatible with the
cochain differentials.  The proof is the generator calculation: the map sends
`b ⊗ (a ⊗ x)` to `(ι(a) * b) ⊗ x`; balancing, unit identities, and the fact that
coefficient reduction is a ring map prove the inverse, differential, and transition
identities.  This statement is strictly degreewise; the parent theorem performs
the whole-complex assembly.
(blueprint: stage3-pur-scalar-quotient-association-degree-data). -/
theorem quotientAssociation_degreeData_exists
    (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (A : CoefficientExtensionSystems.{u, u} l E L ι W)
    (A0 : CoefficientExtensionSystems.{u, u} l E E (AlgHom.id ℚ_[l] E) W)
    (d : CoefficientExtensionReductionData.{u, u} l E L ι W SE SL A)
    (d0 : CoefficientExtensionReductionData.{u, u} l E E (AlgHom.id ℚ_[l] E) W SE SE A0)
    (K : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory) :
    ∃ (δ : ∀ i : ℤ, ((scalar l E L ι W).obj (d0.direct.obj K)).X i ≅
        (d.direct.obj K).X i),
      (∀ (i j : ℤ),
        (δ i).hom ≫ (d.direct.obj K).d i j =
          ((scalar l E L ι W).obj (d0.direct.obj K)).d i j ≫ (δ j).hom) ∧
      ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
        (b : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
        (a : (coefficientSequenceCommRingSheaf l E W).obj.obj (op (n, U.unop)))
        (x : (K.obj.X i).val.obj U),
        (δ i).hom.val.app (op (n, U.unop))
          (integralComparisonSequenceTensorSection l E L ι W ((d0.direct.obj K).X i)
            (op (n, U.unop)) b
            (integralComparisonSequenceSection.{u, u} l E W ((d0.direct.obj K).X i) n U
              ((((d0.directEvaluation n).inv.app K).f i).val.app U
                (integralScalarTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) W n
                  (K.obj.X i) U a x)))) =
        integralComparisonSequenceSection.{u, u} l L W ((d.direct.obj K).X i) n U
          ((((d.directEvaluation n).inv.app K).f i).val.app U
            (integralScalarTensorSection.{u, u} l E L ι W n (K.obj.X i) U
              (((integralComparisonSequenceScalarMap.{u, u} l E L ι W).hom.app
                (op (n, U.unop))) a * b) x)) := by
  sorry

end WeilConjectures.ScalarExtensionTower
