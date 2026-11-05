/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.SmoothPurity.Supporting.Scalar.OrdinaryScalarEvaluationUnit
import WeilConjectures.SmoothPurity.Scalar.ScalarCochainEvaluationOfUnit

/-! # Evaluation of the scalar-extension cochain counit

Source: Stacks 03D7, 06YY and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
-- Keep the common constant-sheaf and localization constructions abstract when
-- comparing the generic evaluation with its coefficient-system specialization.
attribute [local irreducible] constantSheaf CategoryTheory.Functor.leftAdjoint
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

variable (A : CoefficientExtensionSystems l E L ι W)

/-- The ordinary scalar evaluation comparison respects the actual adjunction units.
Source: Stacks 03D7 and 07A6
(blueprint: stage3-pur-scalar-cochain-evaluation). -/
@[irreducible] def IsCoefficientScalarEvaluationUnit
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E) : Prop :=
  ∀ (n : ℕ) (M : coefficientSequenceModules l E W),
    (coefficientSequenceEvaluation l E W n).map
        (A.scalar.ordinaryAdjunction.unit.app M) ≫
      (SemilinearSections.restrictionEvaluation_existsUnique.{t + 1, t, max (t + 1) u}
        (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W) (coefficientSequenceCommRingTransition l E W)
        (integralCoefficientCommRingSheaf l L W) (coefficientSequenceCommRingTransition l L W)
        (integralScalarQuotientSheafMap l E L ι W)
        (coefficientExtensionQuotient_naturality l E L ι W) n).exists.choose.hom.app
          (A.scalar.model.E.obj M) ≫
      (SemilinearSections.res (integralScalarQuotientSheafMap l E L ι W n)).map
        ((ρ n).hom.app M) =
      (A.levels n).ordinaryAdjunction.unit.app
        ((coefficientSequenceEvaluation l E W n).obj M)

end WeilConjectures
