# integralComparisonCounitCharacterization

## Reason

The original public import of StrictRoosComparison is unused by every statement,
definition, and new proof in the item. The normalized Roos model is already supplied
by IntegralComparisonRealizationModels. Remove this planned-proof import rather than
retaining an unused public dependency.

## Old

```lean
public import Sheaf.CategoryTheory.StrictRoosComparison
```

## New

The unused import is removed. All existing declaration signatures, visibility,
attributes and definition bodies are unchanged.

## Users

`python3 tools/downstream.py Sheaf.TraceFormula.IntegralComparisonCounitCharacterization
--uses integralComparisonCounitCharacterization` reports zero downstream modules;
the only textual use is the declaration in this module itself. The item remains
attached to its DAG node and is not withdrawn. Its DAG parents with unfinished
proofs continue to use the same public declarations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | K4 | Remove unused public import; prove both existing theorems. |

No target definition or signature changes, so no target statement review is reopened.

## Status

landed 20261021T203657-L-3851647 2026-10-21 (merge of deliver/K4/Sheaf.TraceFormula.IntegralComparisonCounitCharacterization)
