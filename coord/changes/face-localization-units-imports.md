# Algebra.isAddUnit_addLocalization_iff_face imports

## Reason

The statement and the complete proof use only Mathlib's additive monoid localization
API. Remove the unrelated log-geometric public import and replace the group-completion
public import by the smaller localization module. No declaration signature, definition,
attribute or visibility changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
```

## New

```lean
public import Mathlib.GroupTheory.MonoidLocalization.Basic
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FaceLocalizationUnits | Q1 | Complete the proof using Basic alone. |
| Sheaf.TraceFormula.FsFaceSharpening | unclaimed | No adaptation: its public import of FaceLocalizationFs already publicly imports both removed modules. |

`tools/downstream.py Sheaf.AlgebraicGeometry.FaceLocalizationUnits --uses
Algebra.isAddUnit_addLocalization_iff_face` reports no declaration users outside the
item, and 50 downstream modules. A source import search finds exactly one direct
importer, `Sheaf.TraceFormula.FsFaceSharpening`. Its unchanged public import of
`Sheaf.TraceFormula.FaceLocalizationFs` preserves both old imports for all downstream
modules. No target statement or definition changes meaning.

## Status

landed 20261023T103158-L-3069024 2026-10-23 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.FaceLocalizationUnits)
