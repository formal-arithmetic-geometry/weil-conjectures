# CategoryTheory.FlatScalarTowerLimit.flatScalarTowerLimitSquare

## Reason

The proof needs only the coefficient diagram definitions and the supplied normalized
comparison structures. Remove theorem-module public imports unused by the statement
and proof. The new private helpers also use elaboration options and a scoped `omit`.
No public declaration signature, definition body, attribute, or instance changes.

## Old

```lean
public import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
public import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
public import Sheaf.CategoryTheory.ExactAdjointTowerModels
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
```

The existing option commands were:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
```

## New

```lean
public import Sheaf.CategoryTheory.FlatRingedDiagramRestrictionDefs
public import Sheaf.CategoryTheory.ExactAdjointTowerModels
```

The option commands are:

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
```

Each of the new private normalization-calculus theorem and the public item theorem
uses the following elaboration bound, with a reason comment at the command:

```lean
set_option maxHeartbeats 700000 in
```

The compiler wall-time limit stays at 60 seconds.

The declaration-local command

```lean
omit [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)] in
```

applies only to the new private proved helper `scalarComparison_exists`.
The options affect elaboration in this file; the `omit` removes unused section
instances from that helper. All existing public declarations retain their types.
There is no mathematical definition repair and no target meaning changes.

## Users

`tools/downstream.py Sheaf.CategoryTheory.FlatScalarTowerLimitSquare` lists one consumer.
It already explicitly imports `Sheaf.CategoryTheory.FlatRingedDiagramRestriction` and
`Sheaf.Paper.CompletedDirectImageLimits`; its statement uses none of the removed
public theorem declarations. It needs no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FlatScalarTowerLimitSquare | V6 | Item proof and import pruning. |
| Sheaf.Paper.CompletedScalarUnitAdjunction | A9 | Public item interfaces unchanged; no adaptation. |

## Status

landed 20261021T204038-L-3926821 2026-10-21 (merge of deliver/V6/Sheaf.CategoryTheory.FlatScalarTowerLimitSquare)
