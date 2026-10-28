# WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare_of_representativeTransport

## Reason

The old representative premise quantified over every morphism beta, including zero.
The existing compiled diagnostic identifies this with unintended vanishing on complete
inputs. Use the specified ordinary tensorator and scalar-completion maps instead.
This is the canonical square before cancelling source completion. The completed
conclusion in every module above the two repaired lemmas remains the same.

The implication is reproved by transport of two natural transformations along the
essentially surjective product good localization, then cancellation of source completion.
The private completion-unit identity is proved independently of the remaining hole.

## Old

```lean
theorem scalarTowerTensorLimitSquare_of_representativeTransport
    (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (_hl : IsUnit (l : Γ(W, ⊤)))
    (M N : sfIntegralConstructibleCategory l E W)
    (hT : IsSfDerivedComplete l E W
      ((integralCompletedTensor.{u, u} l E W).obj (M.obj, N.obj)))
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (hRep : ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
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
              SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj Q)))) :
    (scalarTensorCompleted l E L ι W M.obj N.obj M.property.1 N.property.1 hT).hom ≫
        TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι W).obj M.obj,
            (integralScalarExtension.{u} l E L ι W).obj N.obj) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY M.obj)
            (scalarReduction l E L ι W SE SL ρL SY N.obj))) =
      SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E W).obj (M.obj, N.obj)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
            (tensorReduction l E W SE ρE TE M.obj N.obj) ≫
          α.hom.app (SE.reduction.obj M.obj, SE.reduction.obj N.obj))
```

## New

```lean
theorem scalarTowerTensorLimitSquare_of_representativeTransport
    (W : Scheme.{u})
    (SE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (SL : CoefficientDerivedSystemCalculus.{u, u} l L W)
    (ρE : IntegralComparisonRoosModel.{u, u} l E W)
    (ρL : IntegralComparisonRoosModel.{u, u} l L W)
    (SY : IntegralComparisonScalarModel.{u, u} l E L ι W SE ρL)
    (TE : TensorModel l E W SE ρE) (TL : TensorModel l L W SL ρL)
    (_hl : IsUnit (l : Γ(W, ⊤)))
    (M N : sfIntegralConstructibleCategory l E W)
    (hT : IsSfDerivedComplete l E W
      ((integralCompletedTensor.{u, u} l E W).obj (M.obj, N.obj)))
    (α : SE.systemClosed.tensor ⋙ integralComparisonDerivedSequenceScalar.{u, u} l E L ι W ≅
      (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).prod
        (integralComparisonDerivedSequenceScalar.{u, u} l E L ι W) ⋙ SL.systemClosed.tensor)
    (hRep : ∀ (P Q : (integralOperationsGoodComplex l E W).FullSubcategory),
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
              SE.reduction.obj ((integralOperationsGoodLocalization l E W).obj Q)))) :
    (scalarTensorCompleted l E L ι W M.obj N.obj M.property.1 N.property.1 hT).hom ≫
        TL.realization.hom.app
          ((integralScalarExtension.{u} l E L ι W).obj M.obj,
            (integralScalarExtension.{u} l E L ι W).obj N.obj) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          (SL.systemClosed.tensor.map (Prod.mkHom
            (scalarReduction l E L ι W SE SL ρL SY M.obj)
            (scalarReduction l E L ι W SE SL ρL SY N.obj))) =
      SY.realization.hom.app
          ((integralCompletedTensor.{u, u} l E W).obj (M.obj, N.obj)) ≫
        (coefficientSequenceLimit.{u, u} l L W).map
          ((integralComparisonDerivedSequenceScalar.{u, u} l E L ι W).map
            (tensorReduction l E W SE ρE TE M.obj N.obj) ≫
          α.hom.app (SE.reduction.obj M.obj, SE.reduction.obj N.obj))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ScalarTowerTensorLimitStrictEquationAssembly` | unclaimed | Statement repair; complete replacement proof; zero holes. |
| `Sheaf.Paper.ScalarTowerTensorLimitTransportAssembly` | unclaimed | Only declaration consumer in the downstream source scan; its exact original proof compiles against the two repaired statements. No delivered edit. |

The current claim list was read before adapting the unclaimed module. The user-facing
target signatures and all definitions are unchanged. No target-definition re-review
is required. The module-level downstream scan is large, but the declaration-name
scan has only the users listed here. Direct importers and users are compiled against
the changed dependency chain, with further checks performed by the delivery tool.

## Status

landed 20261028T072339-L-1935707 2026-10-28 (merge of deliver/B2/Sheaf.Paper.ScalarTowerTensorLimitRepresentativeTransport)
