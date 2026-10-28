# scalarPullbackRightRoos_normalized

## Reason

The original split discarded the tensor-unit hypothesis on q. Its conclusion
cannot hold for arbitrary q: replacing q by q followed by negation negates the
left side and leaves the right side fixed. On a nonempty geometric point, take
identity pullback and coefficient embedding and a nonzero completed rank-one
object. The ordinary comparison is nonzero, so the two signs cannot both satisfy
the asserted equality. The parent already assumes ScalarPullbackQuotientFormula.
Restore that hypothesis at the normalization theorem and pass it from the parent.
No Challenge target or source-library declaration changes.

The corrected proof separates off scalarPullbackCompletionRoos, the augmentation
and quotient-coordinate calculation with no scalar realization model, no scalar
completion inverse and no completeness assumption. Scalar model normalization,
completion normalization, naturality and invertible cancellation are proved in
the item. This is a decomposition of the corrected statement, not a proof of the
old false statement.

## Old

```lean
theorem scalarPullbackRightRoos_normalized (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L (W true))
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true) (ME.calculus true) ρ)
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (P : (integralOperationsGoodComplex.{u, u} l E (W false)).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E (W false))
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E (W false)) ℤ)
    (eC : (ME.calculus false).reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W false) n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W false) n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E (W false)
      (ME.calculus false).toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E (W false)
      (ME.calculus false) P.obj C eC κ)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L (W true)).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W false)).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι (W false)).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hF : IsSfDerivedComplete l E (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj)) :
    (SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj K.obj) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
          (pullbackReduction l E W ME f K.obj))) ≫
      scalarPullbackRoosCoordinate l E L ι f P C (ME.calculus false) ρ K.obj eP eC q =
    (scalarCompletionIso l E L ι (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj) hF).inv ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullback.{u, u} l E f).map eP.inv) ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullbackComparison.{u, u} l E f).hom.app P) ≫
      (integralOrdinaryScalar l E L ι (W true)).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor.{u, u} l E f).obj P.obj) ≫
      DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj)
```

## New

```lean
theorem scalarPullbackRightRoos_normalized (W : Bool → Scheme.{u})
    (ME : CompletedOperations.Models.{u, u} l E W)
    (ρ : IntegralComparisonRoosModel.{u, u} l L (W true))
    (SX : IntegralComparisonScalarModel.{u, u} l E L ι (W true) (ME.calculus true) ρ)
    (f : W true ⟶ W false)
    (_hX : IsUnit (l : Γ(W true, ⊤))) (_hY : IsUnit (l : Γ(W false, ⊤)))
    (P : (integralOperationsGoodComplex.{u, u} l E (W false)).FullSubcategory)
    (K : sfIntegralConstructibleCategory l E (W false))
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (C : CochainComplex (coefficientSequenceModules.{u, u} l E (W false)) ℤ)
    (eC : (ME.calculus false).reduction.obj (DerivedCategory.Q.obj P.obj) ≅ DerivedCategory.Q.obj C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation.{u, u} l E (W false) n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex.{u, u} l E (W false) n).obj P.obj)
    (hp : CoefficientReductionPresentation.{u, u} l E (W false)
      (ME.calculus false).toCoefficientDerivedSystemReduction P.obj P.property.1 C eC κ)
    (hc : IsIntegralComparisonPresentationCoherent.{u, u} l E (W false)
      (ME.calculus false) P.obj C eC κ)
    (q :
    (((coefficientSequenceRestriction.{u, u} l L (W true)).mapHomologicalComplex (.up ℤ)).obj
      ((((integralComparisonSequencePullback.{u, u} l L f).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequenceScalarModel.{u, u} l E L ι (W false)).E.mapHomologicalComplex
          (.up ℤ)).obj C)))).asFunctor ≅
      (integralOperationsPullbackTowerFunctor.{u, u} l L f).obj
        (((integralOrdinaryScalar l E L ι (W false)).mapHomologicalComplex (.up ℤ)).obj P.obj))
    (hq : ScalarPullbackQuotientFormula l E L ι f P C κ q)
    (hF : IsSfDerivedComplete l E (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj)) :
    (SX.realization.hom.app ((integralDerivedPullback.{u, u} l E f).obj K.obj) ≫
      (coefficientSequenceLimit.{u, u} l L (W true)).map
        ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι (W true)).map
          (pullbackReduction l E W ME f K.obj))) ≫
      scalarPullbackRoosCoordinate l E L ι f P C (ME.calculus false) ρ K.obj eP eC q =
    (scalarCompletionIso l E L ι (W true)
      ((integralDerivedPullback.{u, u} l E f).obj K.obj) hF).inv ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullback.{u, u} l E f).map eP.inv) ≫
      (integralOrdinaryDerivedScalar l E L ι (W true)).map
        ((integralDerivedPullbackComparison.{u, u} l E f).hom.app P) ≫
      (integralOrdinaryScalar l E L ι (W true)).mapDerivedCategoryFactors.hom.app
        ((integralOperationsPullbackComplexFunctor.{u, u} l E f).obj P.obj) ≫
      DerivedCategory.Q.map (scalarPullbackChain l E L ι f P.obj)
```

The new public theorem
WeilConjectures.ScalarExtensionTower.scalarPullbackCompletionRoos is in the new
module Sheaf.Paper.ScalarPullbackCompletionRoos. Its statement is recorded in
lem-pur-scalar-pullback-completion-roos. It is imported privately by the item.
There are no new public instances or attributes, and no public imports change.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarPullbackRightRoos | unclaimed at the server check | pass its existing hq to the repaired normalization theorem; signature unchanged |
| Sheaf.Paper.ScalarPullbackRightRoosNormalization | A5 | privately imports and uses the independent augmentation calculation |
| Sheaf.Paper.ScalarTowerPullbackLimitBridge | unchanged indirect consumer | imports the right-route theorem, whose statement is unchanged |

The right-route node's proof now records the use of hq. The item's node has a
statement_change with the exact old statement and a complete citer audit: its
sole citer is stage3-pur-scalar-pullback-right-roos, whose existing hypothesis
supplies the added argument. The unit route is unchanged (its realized lists are
empty for this conventions unit).

The original caller was compiled against the new normalization signature and
fails at the old call: hF has type IsSfDerivedComplete but the next argument must
have type ScalarPullbackQuotientFormula. Passing the existing hq is the sole
necessary call-site adaptation; the discarded `have _hq := hq` is removed.

## Status

landed 20261028T055603-L-770190 2026-10-28 (merge of deliver/A5/Sheaf.Paper.ScalarPullbackRightRoosNormalization)
