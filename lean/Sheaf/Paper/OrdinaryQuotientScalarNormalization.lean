/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CompletionUnitModels
import all Sheaf.Paper.OrdinaryQuotientScalarTowerConstruction
import all Sheaf.Paper.OrdinaryQuotientScalarSections
import all Sheaf.Paper.CoefficientExtensionAssociationTensorCoordinates

/-! # Presentation sections in ordinary scalar towers

Source: Stacks 03D7, 03EK and 0941, naturality of ordinary tensor adjunction units.
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
  SemilinearSections.systemMap CategoryTheory.Functor.leftAdjoint HasDerivedCategory.standard
attribute [local implicit_reducible] direct integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  Functor.mapHomologicalComplex HomologicalComplex.complexOfFunctorsToFunctorToComplex

/-- The finite balanced comparison takes scalar multiples of quotient units to tensors.
Source: Stacks 03D7 and 03EK, the normalized balanced associator.
(blueprint: lem-trf-ordinary-quotient-scalar-tensor-normalization).
Proof: apply the forward comparison to its proved inverse-coordinate tensor
formula and cancel the inverse isomorphism. This calculation holds for every
completed module, scalar and section, with no flatness condition. -/
private theorem finiteComparison_unit
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
    coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
    scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
      integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (K : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L W n).obj.obj U) (x : K.val.obj U) :
    ((finiteComparison l E L ι W A M ρ association n).hom.app K).val.app U
      (s • CoefficientExtensionAssociation.evaluatedUnitSection l E L ι W A ρ
        (M.tensor.obj K) n U
          (CoefficientExtensionAssociation.quotientUnitSection l E W M K n U x)) =
      integralScalarTensorSection l E L ι W n K U s x := by
  have h := CoefficientExtensionAssociation.association_inverse_tensor l E L ι W A M ρ
    association hassociation K n U s x
  exact (congrArg
    (fun y ↦ ((finiteComparison l E L ι W A M ρ association n).hom.app K).val.app U y)
    h.symm).trans
      (congrArg (fun f ↦ f.val.app U (integralScalarTensorSection l E L ι W n K U s x))
        ((finiteComparison l E L ι W A M ρ association n).app K).inv_hom_id)

private theorem comparison_section
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (e : ((direct l E L ι W A M) ⋙
        (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex).obj P ≅
      (integralScalarTowerFunctor l E L ι W).obj P)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (he : e.hom.app (op n) =
      (coefficientRestrictedComplexEvaluation l L W n).hom.app
        ((direct l E L ι W A M).obj P) ≫
      ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ)).map
        ((directEvaluation l E L ι W A M ρ association n).hom.app P))
    (y : (A.scalar.model.E.obj (M.tensor.obj (P.X i))).val.obj (op (n, U.unop)))
    (z : ((coefficientSequenceEvaluation l L W n).obj
      (A.scalar.model.E.obj (M.tensor.obj (P.X i)))).val.obj U)
    (hy : HEq y z) :
    ((e.hom.app (op n)).f i).val.app U
      (integralComparisonRestrictedSection l L W
        (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y) =
      ((finiteComparison l E L ι W A M ρ association n).hom.app (P.X i)).val.app U z := by
  rw [he]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    restrictedEvaluation_hom_f, directEvaluation_hom_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have ht : HEq
      ((((eqToIso (coefficientSequenceRestriction_evaluation l L W n)).app
        (A.scalar.model.E.obj (M.tensor.obj (P.X i))))).hom.val.app U
          (integralComparisonRestrictedSection l L W
            (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y)) z :=
    (heq_of_eq (restrictionEvaluation_section l L
      (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y)).trans
        ((evaluation_section_heq l L
          (A.scalar.model.E.obj (M.tensor.obj (P.X i))) n U y).trans hy)
  simp only [Iso.app_hom, eqToIso.hom, eqToHom_app] at ht
  exact eq_of_heq (restrictionMap_apply_heq l L W n
    ((finiteComparison l E L ι W A M ρ association n).hom.app (P.X i)) U _ z ht)

private theorem normalizedComparison
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    (F : coefficientSequenceModules l E W ⥤ coefficientSequenceModules l L W)
    [F.Additive] (hF : A.scalar.model.E = F) :
    let T := F.mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    ∃ θ : M.quotient l E W ⋙ T ≅ integralScalarTowerFunctor l E L ι W,
      ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ)
        (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
        (a : (M.quotient l E W).obj P ≅ C)
        (κ : ∀ n : ℕ,
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
            (unrestrictedIntegralFiniteComplex l E W n).obj P),
        (∀ n : ℕ,
          ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
            κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) →
        ∀ (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ)
          (s : (coefficientSequenceCommRingSheaf l L W).obj.obj (op (n, U.unop)))
          (x : (P.X i).val.obj U)
          (y : (F.obj (C.X i)).val.obj (op (n, U.unop))),
          HEq y (s • (show (A.scalar.model.E.obj (C.X i)).val.obj (op (n, U.unop)) from
            (A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app (op (n, U.unop))
              (integralComparisonSequenceSection l E W (C.X i) n U
                (((κ n).inv.f i).val.app U
                  (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))))) →
          (((T.mapIso a.symm ≪≫ θ.app P).hom.app (op n)).f i).val.app U
            (integralComparisonRestrictedSection l L W (F.obj (C.X i)) n U y) =
            integralScalarTensorSection l E L ι W n (P.X i) U s x := by
  subst F
  dsimp only
  obtain ⟨θ, hθ⟩ := comparison_exists l E L ι W A M ρ hρ association hassociation
  refine ⟨θ, ?_⟩
  intro P C a κ hκ n i U s x y hy
  let w := integralComparisonSequenceSection l E W (C.X i) n U
    (((κ n).inv.f i).val.app U
      (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))
  have hp := presentationUnit l E W M P C a κ hκ n i U x
  have hn := congrArg (fun f ↦ f.val.app (op (n, U.unop)) w)
    (A.scalar.ordinaryAdjunction.unit.naturality (a.inv.f i))
  have hy' := eq_of_heq hy
  subst y
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapIso_hom,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [restriction_map_section l L
    (A.scalar.model.E.map (a.inv.f i)) n U]
  change (A.scalar.ordinaryAdjunction.unit.app (M.tensor.obj (P.X i))).val.app
      (op (n, U.unop)) ((a.inv.f i).val.app (op (n, U.unop)) w) =
    (A.scalar.model.E.map (a.inv.f i)).val.app (op (n, U.unop))
      ((A.scalar.ordinaryAdjunction.unit.app (C.X i)).val.app (op (n, U.unop)) w) at hn
  rw [hp] at hn
  dsimp only [w] at hn
  erw [map_smul, ← hn]
  have hu := evaluatedUnit_smul_raw l E L ι W A ρ hρ (M.tensor.obj (P.X i)) n U s
    (CoefficientExtensionAssociation.quotientUnitSection l E W M (P.X i) n U x)
  exact (comparison_section l E L ι W A M ρ association P (θ.app P) n i U
    (hθ P n) _ _ hu).trans
      (finiteComparison_unit l E L ι W A M ρ association hassociation (P.X i) n U s x)

end OrdinaryScalarTowerProof
end WeilConjectures
