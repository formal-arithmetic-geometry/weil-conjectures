# WeilConjectures.ScalarExtensionTower.scalarPullbackRoosCoordinate_system

## Reason

The inverse system comparison and explicit Roos coordinate form a self-contained proved calculation. Profiling the combined upper proof identified expensive coefficient-functor elaboration and kernel checking; this calculation is compiled separately after sharing the good scalar presentation and avoiding substitution through the whole upper proof.

## Old

Not present: this is a new declaration. No existing signature is changed.

## New

In the existing ambient variables l, E, L and iota (the same prime and finite
coefficient-field hypotheses as the item):

```lean
theorem scalarPullbackRoosCoordinate_system
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : (integralOperationsGoodComplex.{u, u} l E Y).FullSubcategory)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E Y) ℤ)
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E Y)
    (ρ : IntegralComparisonRoosModel.{u, u} l L X)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E Y))
    (eP : DerivedCategory.Q.obj P.obj ≅ K)
    (eC : SE.reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L X).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι Y).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E Y n).obj P.obj) :
    let T := coefficientSequenceLimit.{u, u} l L X
    let B := integralComparisonDerivedSequencePullback.{u, u} l L f
    let A := integralComparisonDerivedSequenceScalar.{u, u} l E L ι Y
    let β := integralComparisonSystemScalarPullback.{u, u} l E L ι f
    let a := SE.reduction.map eP.inv ≫ eC.hom
    let CS := ((integralComparisonSequenceScalarModel.{u, u} l E L ι Y).E.mapHomologicalComplex
      (.up ℤ)).obj C
    let b :=
      (integralComparisonSequencePullback.{u, u} l L f).mapDerivedCategoryFactors.hom.app CS
    let r := (integralComparisonRoosBridge.{u, u} l L X ρ
      (((integralComparisonSequencePullback l L f).mapHomologicalComplex (.up ℤ)).obj CS)).hom
    let z := DerivedCategory.Q.map (integralOperationsRoosFunctor.map q.hom)
    T.map (β.inv.app (SE.reduction.obj K)) ≫
        scalarPullbackRoosCoordinate l E L ι f P C SE ρ K eP eC q =
      T.map (B.map (A.map a ≫
        (integralComparisonSequenceScalarModel.{u, u} l E L ι Y).ε.app C) ≫ b) ≫ r ≫ z
```

The declaration is in `Sheaf.Paper.ScalarPullbackRoosCoordinateSystem`; its DAG node is
`lem-pur-scalar-pullback-roos-coordinate-system`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ScalarPullbackLeftRoos` | G6 | Uses the new theorem only in its proof. |

No other existing module is changed. The item retains its exact signature and
public imports.

## Status

landed 20261028T020429-L-2509497 2026-10-28 (merge of deliver/G6/Sheaf.Paper.ScalarPullbackLeftRoos)
