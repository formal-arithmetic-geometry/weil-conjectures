# WeilConjectures.ScalarExtensionTower.scalarCompletionQuotientPresentation

## Reason

The upper calculation needs a coherent quotient presentation of ordinary scalar P, together with the tensor-unit and scalarCompletion/reduction equations. The existing declarations do not state this joint source-side transport. This remains the only new named sorry.

## Old

Not present: this is a new declaration. No existing signature is changed.

## New

In the existing ambient variables l, E, L and iota (the same prime and finite
coefficient-field hypotheses as the item):

```lean
theorem scalarCompletionQuotientPresentation (Y : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L Y)
    (ρ : IntegralComparisonRoosModel.{u, u} l L Y)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι Y SE ρ)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (eC : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E Y
      SE.toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E Y SE P.obj C eC κ) :
    let PS := ((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj
    let CS := ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
      (.up ℤ)).obj C
    ∃ (eS : SL.reduction.obj (DerivedCategory.Q.obj PS) ≅ DerivedCategory.Q.obj CS)
      (κS : ∀ n : ℕ,
        ((coefficientSequenceEvaluation.{u, u} l L Y n).mapHomologicalComplex (.up ℤ)).obj CS ≅
          (unrestrictedIntegralFiniteComplex.{u, u} l L Y n).obj PS),
      CoefficientReductionPresentation.{u, u} l L Y SL.toCoefficientDerivedSystemReduction
        PS (scalarGood l E L ι Y P).1 CS eS κS ∧
      IsIntegralComparisonPresentationCoherent.{u, u} l L Y SL PS CS eS κS ∧
      (∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (P.obj.X i).val.obj (op U)),
        ((κS n).hom.f i).val.app (op U)
          (coefficientEvaluationSection.{u, u} l L Y (CS.X i) n (op U)
            (integralComparisonSequenceTensorSection.{u, u} l E L ι Y (C.X i)
              (op (n, U)) 1
              (integralComparisonSequenceSection.{u, u} l E Y (C.X i) n (op U)
                (((κ n).inv.f i).val.app (op U)
                  (unrestrictedIntegralTensorSection.{u, u} l E Y n (P.obj.X i)
                    (op U) 1 x))))) =
          unrestrictedIntegralTensorSection.{u, u} l L Y n (PS.X i) (op U) 1
            (integralOrdinaryTensorSection l E L ι Y (P.obj.X i) (op U) 1 x)) ∧
      SL.reduction.map
          ((integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj) ≫
        eS.hom =
      SL.reduction.map ((scalarCompletion l E L ι Y).app (DerivedCategory.Q.obj P.obj)) ≫
        scalarReduction l E L ι Y SE SL ρ SY (DerivedCategory.Q.obj P.obj) ≫
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι Y).map eC.hom ≫
        (integralComparisonSequenceScalarModel.{u, u} l E L ι Y).ε.app C
```

The declaration is in `Sheaf.Paper.ScalarCompletionQuotientPresentation`; its DAG node is
`lem-pur-scalar-completion-quotient-presentation`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ScalarPullbackLeftRoos` | G6 | Uses the new theorem only in its proof. |

No other existing module is changed. The item retains its exact signature and
public imports.

## Status

landed 20261028T020429-L-2509497 2026-10-28 (merge of deliver/G6/Sheaf.Paper.ScalarPullbackLeftRoos)
