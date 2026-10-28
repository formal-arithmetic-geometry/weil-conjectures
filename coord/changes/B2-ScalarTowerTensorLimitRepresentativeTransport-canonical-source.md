# WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare_on_good_representatives

## Reason

The old representative premise quantified over every morphism beta, including zero.
The existing compiled diagnostic identifies this with unintended vanishing on complete
inputs. Use the specified ordinary tensorator and scalar-completion maps instead.
This is the canonical square before cancelling source completion. The completed
conclusion in every module above the two repaired lemmas remains the same.

The normalized representative assertion keeps one named theorem hole with its complete
proof plan. This correction is not claimed as closing that hole or as a decomposition.
A new proved private helper expands scalarTensorCompleted and cancels its source
completion isomorphism; the old diagnostic is retained.

## Old

```lean
theorem scalarTowerTensorLimitSquare_on_good_representatives (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (_hstrict : DerivedSigmaModel l E L ι W SE SL α) :
    ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
      (β : (integralScalarExtensionOfUniverses l E L ι W).obj
          ((integralCompletedTensor l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ⟶
        (integralCompletedTensor l L W).obj
          ((integralScalarExtension l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj P),
            (integralScalarExtension l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj Q))),
      β ≫ TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj P),
            (integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj P))
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj Q)))) =
      SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
            (tensorReduction l E W SE ρE TE
              ((integralOperationsGoodLocalization l E W).obj P)
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
          α.hom.app
            (SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj P),
              SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj Q)))
```

## New

```lean
theorem scalarTowerTensorLimitSquare_on_good_representatives (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (hstrict : DerivedSigmaModel l E L ι W SE SL α) :
    ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
      (scalarTensorOrdinary l E L ι W).hom.app
          ((integralOperationsGoodLocalization l E W).obj P,
            (integralOperationsGoodLocalization l E W).obj Q) ≫
        (integralCompletedTensor l L W).map (Prod.mkHom
          ((scalarCompletion l E L ι W).app
            ((integralOperationsGoodLocalization l E W).obj P))
          ((scalarCompletion l E L ι W).app
            ((integralOperationsGoodLocalization l E W).obj Q))) ≫
        TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj P),
            (integralScalarExtension.{u} l E L ι W).obj
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj P))
            (scalarReduction l E L ι W SE SL ρL SY
              ((integralOperationsGoodLocalization l E W).obj Q)))) =
      (scalarCompletion l E L ι W).app
          ((integralCompletedTensor l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ≫
        SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E W).obj
            ((integralOperationsGoodLocalization l E W).obj P,
              (integralOperationsGoodLocalization l E W).obj Q)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
            (tensorReduction l E W SE ρE TE
              ((integralOperationsGoodLocalization l E W).obj P)
              ((integralOperationsGoodLocalization l E W).obj Q)) ≫
          α.hom.app
            (SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj P),
              SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj Q)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ScalarTowerTensorLimitRepresentativeTransport` | B2 | Statement repair; one existing hole retained. |
| `Sheaf.Paper.ScalarTowerTensorLimitTransportAssembly` | unclaimed | Only declaration consumer in the downstream source scan; its exact original proof compiles against the two repaired statements. No delivered edit. |
| `Sheaf.Paper.ScalarTowerTensorLimitStrictEquationAssembly` | unclaimed | New private proof import accesses only the independently proved completion-unit helper. Its premise changes to the corrected natural equation in this delivery. |

The current claim list was read before adapting the unclaimed module. The user-facing
target signatures and all definitions are unchanged. No target-definition re-review
is required. The module-level downstream scan is large, but the declaration-name
scan has only the users listed here. Direct importers and users are compiled against
the changed dependency chain, with further checks performed by the delivery tool.

## Status

landed 20261028T072339-L-1935707 2026-10-28 (merge of deliver/B2/Sheaf.Paper.ScalarTowerTensorLimitRepresentativeTransport)
