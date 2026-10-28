# WeilConjectures.ScalarExtensionTower.scalarPullbackQuotient_ext

## Reason

The normalized L-pullback presentation supplies a strict comparison that must be identified with the supplied q. This new proved theorem detects equality from the nested tensor-unit formula by three ordinary adjunctions and local surjectivity of completed coefficient projection.

## Old

Not present: this is a new declaration. No existing signature is changed.

## New

In the existing ambient variables l, E, L and iota (the same prime and finite
coefficient-field hypotheses as the item):

```lean
theorem scalarPullbackQuotient_ext {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (q' :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hq : ScalarPullbackQuotientFormula l E L ι f P C κ q)
    (hq' : ScalarPullbackQuotientFormula l E L ι f P C κ q') : q = q'
```

The declaration is in `Sheaf.Paper.ScalarPullbackQuotientExt`; its DAG node is
`lem-pur-scalar-pullback-quotient-ext`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ScalarPullbackLeftRoos` | G6 | Uses the new theorem only in its proof. |

No other existing module is changed. The item retains its exact signature and
public imports.

## Status

landed 20261028T020429-L-2509497 2026-10-28 (merge of deliver/G6/Sheaf.Paper.ScalarPullbackLeftRoos)
