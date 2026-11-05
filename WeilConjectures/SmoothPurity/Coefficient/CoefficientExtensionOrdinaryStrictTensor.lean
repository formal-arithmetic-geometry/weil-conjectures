/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import all WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import all WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined

/-! # Ordinary strict finite coefficient tensor models

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  SheafOfModules.monoidalCategory integralScalarReduction

section TensorNormalization
universe c v r
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}

end TensorNormalization

section FunctorTransport
universe c cv d dv r
variable {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]
  {J : GrothendieckTopology D} {R : Sheaf J RingCat.{r}}

end FunctorTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

section EvaluationTransport
attribute [local irreducible] constantSheaf coefficientSequenceCommRingSheaf
  coefficientEvaluationSystem

end EvaluationTransport

@[irreducible] private def scalarCoefficientEvaluation (n : ℕ) :
    scalarCoefficientExtension l E L ι W ⋙ coefficientSequenceEvaluation l L W n ≅
      integralScalarReduction l E L ι W n := by
  let F := SheafOfModules.SequenceProjection.extension
    (completedIntegralCommRingSheafUnrestricted l E W)
    (coefficientSequenceCommRingSystem l L W) (scalarCoefficientCone l E L ι W)
  let G := SheafOfModules.strictSystemToSequenceFunctor (coefficientSequenceCommRingSystem l L W)
  let B := coefficientSequenceCommRingSystem l L W
  let a : F ⋙ G ⋙ coefficientSequenceEvaluation l L W n ≅
      F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n :=
    Functor.isoWhiskerLeft (scalarCoefficientExtension l E L ι W)
      (coefficientEvaluationIso l L W n)
  let b : F ⋙ G ⋙ SheafOfModules.systemSequenceEvaluation B n ≅
      F ⋙ SheafOfModules.systemEvaluation B n :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.strictSystemSequenceUnitLevel B
      (F.obj M) n).symm) (by intros; ext U x; rfl)
  let c : F ⋙ SheafOfModules.systemEvaluation B n ≅
      integralScalarReductionConcrete l E L ι W n :=
    NatIso.ofComponents (fun M ↦
      SheafOfModules.SequenceProjection.extensionIso
        (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) M n)
      (by
        intro M N f
        exact extensionIso_naturality
          (completedIntegralCommRingSheafUnrestricted l E W) B
          (scalarCoefficientCone l E L ι W) f n)
  exact a ≪≫ b ≪≫ c ≪≫ (integralScalarReductionIso l E L ι W n).symm

attribute [local irreducible] constantSheaf coefficientSequenceCommRingSheaf
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  integralScalarRho
  SheafOfModules.SequenceProjection.extensionIso integralScalarReductionIso
  SheafOfModules.strictSystemSequenceUnitLevel SheafOfModules.systemModelTmul

section TransitionSections

end TransitionSections

attribute [local irreducible] scalarCoefficientExtension

attribute [local semireducible] scalarCoefficientExtension
attribute [local irreducible] IsCoefficientExtensionStrictTransition

end WeilConjectures
