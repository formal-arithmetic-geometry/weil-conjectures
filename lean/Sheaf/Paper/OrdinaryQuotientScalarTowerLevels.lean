/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CompletionUnitModels
import Sheaf.Paper.CoefficientExtensionAssociationSuccessor
import all Sheaf.Paper.CoefficientExtensionAssociationScalarUnits

/-! # Finite levels of the ordinary scalar tower

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
(blueprint: def-trf-ordinary-quotient-scalar-tower-levels).
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction constantSheaf
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralCoefficientCommRingSheaf

private def finiteComparison
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (n : ℕ) :
    M.tensor ⋙ A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      integralScalarReduction l E L ι W n :=
  Functor.isoWhiskerLeft M.tensor (ρ n) ≪≫
    Functor.isoWhiskerRight (C := scalarReductionSource l E W)
      (D := normalizedDVRModules l E W n) (E := normalizedDVRModules l L W n)
      (M.evaluation n) (A.levels n).model.E ≪≫ association n

private def direct (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W) :
    CochainComplex (scalarReductionSource l E W) ℤ ⥤
      CochainComplex (coefficientSequenceModules l L W) ℤ :=
  M.quotient l E W ⋙ A.scalar.model.E.mapHomologicalComplex (.up ℤ)

private def directEvaluation
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (n : ℕ) :
    direct l E L ι W A M ⋙
      (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
        integralScalarFiniteComplex l E L ι W n :=
  NatIso.ofComponents (fun P ↦ HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (finiteComparison l E L ι W A M ρ association n).app (P.X i)) (by
      intro i j hij
      exact ((finiteComparison l E L ι W A M ρ association n).hom.naturality
        (P.d i j)).symm)) (by
    intro P Q f
    apply HomologicalComplex.hom_ext
    intro i
    exact (finiteComparison l E L ι W A M ρ association n).hom.naturality (f.f i))

private theorem directEvaluation_hom_f
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) (i : ℤ) :
    ((directEvaluation l E L ι W A M ρ association n).hom.app P).f i =
      (finiteComparison l E L ι W A M ρ association n).hom.app (P.X i) := rfl

private theorem directTransition
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) (i : ℤ)
    (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l L W (n + 1)).obj
      (((direct l E L ι W A M).obj P).X i)).val.obj U) :
    HEq (((coefficientSequenceTransition l L W (Nat.le_succ n)).app
      (((direct l E L ι W A M).obj P).X i)).val.app U x)
      ((((directEvaluation l E L ι W A M ρ association n).inv.app P).f i).val.app U
        ((((integralScalarTransition l E L ι W n).app P).f i).val.app U
          ((((directEvaluation l E L ι W A M ρ association (n + 1)).hom.app P).f i).val.app U
            x))) := by
  exact coefficientExtensionAssociation_successor l E L ι W A M ρ hρ
    association hassociation P n i U x

attribute [local irreducible] SemilinearSections.systemMap
  CategoryTheory.Functor.leftAdjoint HasDerivedCategory.standard
attribute [local implicit_reducible] SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf

private theorem coefficientEvaluation_smul
    (N : coefficientSequenceModules l L W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U)
    (x : N.val.obj (op (n, U.unop))) :
    s • (show ((coefficientSequenceEvaluation l L W n).obj N).val.obj U from x) =
      (s • x : N.val.obj (op (n, U.unop))) := by
  change ((eqToHom (coefficientSequenceEvaluationRing_eq l L W n).symm).hom.app U).hom s • x = _
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private theorem evaluatedUnit_raw_eq
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ N n U x =
      (show ((coefficientSequenceEvaluation l L W n).obj
        (A.scalar.model.E.obj N)).val.obj U from
          (A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x) := by
  exact eq_of_heq (CoefficientExtensionAssociation.evaluatedUnitSection_raw
    l E L ι W A ρ hρ N n U x)

private theorem evaluatedUnit_smul_raw
    (A : CoefficientExtensionSystems l E L ι W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (N : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    HEq
      (s • (show (A.scalar.model.E.obj N).val.obj (op (n, U.unop)) from
        (A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x))
      (s • CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ N n U x) := by
  have hr' := evaluatedUnit_raw_eq l E L ι W A ρ hρ N n U x
  have hs := coefficientEvaluation_smul l L W (A.scalar.model.E.obj N) n U s
    (show (A.scalar.model.E.obj N).val.obj (op (n, U.unop)) from
      (A.scalar.ordinaryAdjunction.unit.app N).val.app (op (n, U.unop)) x)
  have hm := congrArg (fun z :
    ((coefficientSequenceEvaluation l L W n).obj (A.scalar.model.E.obj N)).val.obj U ↦
      s • z) hr'.symm
  have hh := hs.symm.trans hm
  exact heq_of_eq hh

end OrdinaryScalarTowerProof
end WeilConjectures
