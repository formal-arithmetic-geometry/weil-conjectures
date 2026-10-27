/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CompletionUnitModels
import all Sheaf.Paper.CoefficientExtensionRestrictedTower
import all Sheaf.Paper.OrdinaryQuotientScalarTowerLevels
import all Sheaf.Paper.CoefficientRingedSequenceSite

/-! # Ordinary scalar tower construction

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
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

attribute [local irreducible] direct directEvaluation finiteComparison

/-- Assemble the explicit finite balanced comparisons into an all-complex tower.
Source: Stacks 03D7, 03EK, and successor compatibility on the sequence site.
(blueprint: lem-trf-ordinary-quotient-scalar-tower-construction).
Proof: restriction-evaluation followed by the finite comparison defines each level.
The given successor identity proves their naturality along adjacent arrows; the
opposite-sequence construction extends this to all arrows. Pointwise inverses
and naturality in the complex give the natural isomorphism and component formula. -/
private theorem comparison_exists
    (A : CoefficientExtensionSystems l E L ι W)
    (M : CompletionUnit.OrdinaryModel l E W)
    (ρ : ∀ n : ℕ, A.scalar.model.E ⋙ coefficientSequenceEvaluation l L W n ≅
      coefficientSequenceEvaluation l E W n ⋙ (A.levels n).model.E)
    (hρ : IsCoefficientScalarEvaluationUnit l E L ι W A ρ)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association)
    :
    let direct := direct l E L ι W A M
    let directEvaluation := directEvaluation l E L ι W A M ρ association
    ∃ e : direct ⋙ (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ) ⋙
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ≅
      integralScalarTowerFunctor l E L ι W,
      ∀ (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ),
        (e.hom.app P).app (op n) =
          (coefficientRestrictedComplexEvaluation l L W n).hom.app (direct.obj P) ≫
            ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ)).map
              ((directEvaluation n).hom.app P) := by
  classical
  let direct := direct l E L ι W A M
  let directEvaluation := directEvaluation l E L ι W A M ρ association
  have htransition := directTransition l E L ι W A M ρ hρ association hassociation
  let H := direct ⋙ (coefficientSequenceRestriction l L W).mapHomologicalComplex (.up ℤ)
  let a (n : ℕ) : H ⋙
      ((evaluation ℕᵒᵖ (scalarReductionSource l L W)).obj (op n)).mapHomologicalComplex
        (.up ℤ) ≅ integralScalarLevel l E L ι W n :=
    Functor.isoWhiskerLeft direct (coefficientRestrictedComplexEvaluation l L W n) ≪≫
      Functor.isoWhiskerRight (directEvaluation n)
        ((scalarReductionRestriction l L W n).mapHomologicalComplex (.up ℤ))
  have ha (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :
      (H.obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op ≫ (a n).hom.app P =
        (a (n + 1)).hom.app P ≫ (integralScalarTransition l E L ι W n).app P := by
    apply (cancel_mono ((a n).inv.app P)).1
    simp only [Category.assoc, Iso.hom_inv_id_app]
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext x
    have hobj (k : ℕ) := congrArg (fun F ↦ F.obj ((direct.obj P).X i))
      (coefficientSequenceRestriction_evaluation l L W k)
    have hs (k : ℕ) :
        ((scalarReductionRestriction l L W k).obj
          ((coefficientSequenceEvaluation l L W k).obj ((direct.obj P).X i))).val.presheaf.obj V =
          ((coefficientSequenceEvaluation l L W k).obj ((direct.obj P).X i)).val.presheaf.obj V :=
      restrictScalars_presheaf_obj _ _ _
    let y : ((coefficientSequenceEvaluation l L W (n + 1)).obj
        ((direct.obj P).X i)).val.obj V :=
      cast (congrArg (fun G : AddCommGrpCat ↦ ↥G)
        ((congrArg (fun M : scalarReductionSource l L W ↦ M.val.presheaf.obj V)
          (hobj (n + 1))).trans (hs (n + 1)))) x
    have hy : HEq y x := by
      exact cast_heq _ x
    have hh := restriction_transition_apply_heq l L W ((direct.obj P).X i)
      (Nat.le_succ n) V x y hy.symm
    have ht := htransition P n i V y
    simp only [a, Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      HomologicalComplex.comp_f, HomologicalComplex.id_f,
      Functor.mapHomologicalComplex_map_f,
      restrictedEvaluation_hom_f, restrictedEvaluation_inv_f]
    erw [Category.comp_id]
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    apply eq_of_heq
    refine (hh.trans ht).trans ?_
    have hc0 := module_eqToHom_apply_heq l L W (hobj (n + 1)) V x
    have hc1 := restrictionMap_apply_heq l L W (n + 1)
      (((directEvaluation (n + 1)).hom.app P).f i) V _ y (hc0.trans hy.symm)
    have hc2 := hcongr_apply rfl
      (HEq.rfl (a := fun x ↦
        ((((integralScalarTransition l E L ι W n).app P).f i).val.app V) x)) hc1
    have hc3 := restrictionMap_apply_heq l L W n
      (((directEvaluation n).inv.app P).f i) V _ _ hc2
    have hc4 := module_eqToHom_apply_heq l L W (hobj n).symm V
      (((((scalarReductionRestriction l L W n).map
        (((directEvaluation n).inv.app P).f i)).val.app V))
          (((((integralScalarTransition l E L ι W n).app P).f i).val.app V)
            (((((scalarReductionRestriction l L W (n + 1)).map
              (((directEvaluation (n + 1)).hom.app P).f i)).val.app V))
                (((eqToHom (hobj (n + 1))).val.app V) x))))
    exact (hc4.trans hc3).symm
  let T := integralScalarTowerFunctor l E L ι W
  obtain ⟨e, he⟩ := assembleTowerIso H T a (fun P n ↦ by
    dsimp only [T, Functor.comp_obj, integralScalarTowerFunctor]
    erw [Functor.flip_obj_map, Functor.ofOpSequence_map_homOfLE_succ]
    exact ha P n)
  refine ⟨e, ?_⟩
  intro P n
  rw [he]
  simp only [a, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rfl

end OrdinaryScalarTowerProof
end WeilConjectures
