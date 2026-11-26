/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionQuotientAssociationDegreeData

/-! # Association of strict coefficient quotient representatives

Strict association `(x ⊗ a) ⊗ b ↦ x ⊗ ι(a) b` for fixed coefficient quotient representatives.

## References

* Stacks Project, Tags 03EL and 07A4.
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

/-- Strict association for fixed quotient representatives, without constructing
models or asserting compatibility with geometric pullback or completed operations. -/
theorem quotientAssociation_exists
    (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (A : CoefficientExtensionSystems.{u, u} l E L ι W)
    (A0 : CoefficientExtensionSystems.{u, u} l E E (AlgHom.id ℚ_[l] E) W)
    (d : CoefficientExtensionReductionData.{u, u} l E L ι W SE SL A)
    (d0 : CoefficientExtensionReductionData.{u, u} l E E (AlgHom.id ℚ_[l] E) W SE SE A0)
    (K : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory) :
    ∃ δ : (scalar l E L ι W).obj (d0.direct.obj K) ≅ d.direct.obj K,
      ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
        (b : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
        (a : (coefficientSequenceCommRingSheaf l E W).obj.obj (op (n, U.unop)))
        (x : (K.obj.X i).val.obj U),
        (δ.hom.f i).val.app (op (n, U.unop))
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
  obtain ⟨δ, hδd, hδ⟩ := quotientAssociation_degreeData_exists l E L ι W SE SL A A0 d d0 K
  let e : (scalar l E L ι W).obj (d0.direct.obj K) ≅ d.direct.obj K :=
    HomologicalComplex.Hom.isoOfComponents δ (by
      intro i j hrel
      exact hδd i j)
  refine ⟨e, ?_⟩
  intro n i U b a x
  exact hδ n i U b a x

end WeilConjectures.ScalarExtensionTower
