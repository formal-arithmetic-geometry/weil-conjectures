/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemGammaProjectionTransportFinal

/-! # Enriched coefficient gamma projection transport

The specialization of `enrichedSequenceProjectionFormula` to the coefficient calculus.

## Implementation details

The coefficient sequence site is identified with the strict system presentation, and the
enriched projection formula is applied to the actual reduction adjunction and tensor comparison.
`D.globalLimit_model`, `D.globalEvaluation_model` and `D.scalarSections_model` transport the
derived sections and limit comparisons, and `H.sections_projection` at the internal-Hom system
gives exactly the `CoefficientGammaProjection` equation.

## References

* [Stacks, Tag 07A6]
* [Stacks, Tag 08JA]
* [Stacks, Tag 0D6E]
* [Stacks, Tag 0941]
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/--
The enriched sequence projection theorem, transported through the coefficient
sequence-site, gives the finite projection identity for `S.gamma`.
-/
theorem coefficientDerivedSystemGammaProjectionTransport
    (S : CoefficientDerivedSystemCalculus l E W)
    (D : CoefficientDerivedSystemResolutionCoherence l E W S)
    (H : CoefficientDerivedSystemProjectionModels l E W S D) :
    CoefficientGammaProjection l E W S D := by
  intro P N hN n
  have hP : IsNormalizedCoefficientSequence l E W (S.reduction.obj P) :=
    S.reduction_normalized P
  let f := S.fiberHom (S.reduction.obj P) N hP hN n
  rw [CoefficientDerivedSystemCalculus.gamma]
  rw [D.globalEvaluation_model (hM := hP)]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, NatTrans.comp_app]
  simp only [Category.assoc]
  simp only [coefficientSequenceGlobalHom]
  have hs := H.sections_projection
    ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N)) n
  have hs' : S.globalLimit.hom.app
      ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N)) ≫
      (coefficientMappingProjection n).app
        ((coefficientSequenceInternalHom l E W ⋙ coefficientSequenceDerivedRestriction l E W ⋙
          (coefficientTowerSections l E W).rightDerivedFunctor).obj (op (S.reduction.obj P), N)) ≫
      (D.systemSectionsEvaluation n).hom.app
        ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N)) =
    (coefficientIntegralSections l E W).map
        ((coefficientSequenceProjection l E W n).app
          ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))) ≫
      (D.scalarSections n).hom.app
        ((coefficientSequenceDerivedEvaluation l E W n).obj
          ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))) := by
    simpa only [Functor.comp_obj] using hs
  have hs'' := congrArg (fun z ↦ z ≫
        (coefficientFiniteSections l E W n).map f.hom) hs'
  have hs''' := congrArg (fun f ↦
      (coefficientIntegralSections l E W).map
        (@asIso _ _ _ _ (coefficientEnrichedAdjunctionMap S.integralClosed
          S.systemClosed S.reduction S.adjunction S.reductionTensor P N)
          (S.enriched_isIso P N hN)).hom ≫ f) hs''
  calc
    _ = (coefficientIntegralSections l E W).map
          (@asIso _ _ _ _ (coefficientEnrichedAdjunctionMap S.integralClosed
            S.systemClosed S.reduction S.adjunction S.reductionTensor P N)
            (S.enriched_isIso P N hN)).hom ≫
        (coefficientIntegralSections l E W).map
          ((coefficientSequenceProjection l E W n).app
            ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))) ≫
        (D.scalarSections n).hom.app
          ((coefficientSequenceDerivedEvaluation l E W n).obj
            ((coefficientSequenceInternalHom l E W).obj (op (S.reduction.obj P), N))) ≫
        (coefficientFiniteSections l E W n).map f.hom := by
      simpa only [Category.assoc, f, Iso.app_hom] using hs'''
    _ = _ := coefficientDerivedSystemGammaProjectionTransport_final
      l E W S D H P N hN n

end WeilConjectures
