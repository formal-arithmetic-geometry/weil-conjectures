# CoefficientExtensionReductionModel intermediate declarations

## Reason

The two target holes require independently stated construction, effectivity, scalar-association, and counit-naturality results. Naming these intermediate results makes each remaining proof obligation a proper theorem with its own DAG node.

## Old

The module exposed only the two target theorems `coefficientExtensionReductionModel` and `coefficientExtensionReduction_composition`; their bodies were `by sorry`.

## New

The module additionally exposes `CoefficientExtensionReductionSkeleton`, `coefficientExtensionReductionSkeleton_exists`, `coefficientExtensionReductionSkeleton_comparison_isIso`, `coefficientExtensionScalarAssociation_exists`, `CoefficientExtensionReductionCompositionEquation`, and `coefficientExtensionReductionCompositionEquation_proved`. The target theorem signatures are unchanged; the targets now assemble these intermediate results.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefficientExtensionReductionModel | Y2 | Defines and consumes the intermediate construction and comparison results |

## Status

landed 20261021T002940-L-1582346 2026-10-21 (merge of deliver/Y2/Sheaf.Paper.CoefficientExtensionReductionModel)
