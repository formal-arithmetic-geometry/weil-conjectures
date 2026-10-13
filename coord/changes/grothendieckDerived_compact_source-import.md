# CategoryTheory.grothendieckDerived_compact_source

## Reason

Remove the unused public import Mathlib.CategoryTheory.Triangulated.Functor.
The signature uses no notion from that module. The compact-generation interface
already publicly imports the triangulated-category definitions. This is an import
interface cleanup only: no declaration statement or definition changes.

## Old

```lean
public import Mathlib.CategoryTheory.Triangulated.Functor
```

## New

The import line is removed. All existing declaration signatures remain identical.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.GrothendieckDerivedCompactLocalizationModel | unclaimed | No adaptation: already explicitly publicly imports Mathlib.CategoryTheory.Triangulated.Functor; statement and proof unchanged. Original consumer compiled against the cleaned module in the reader scratchpad. |

No target statement or definition is changed; no semantic target review is reopened.

## Status

landed 20261013T190136-L-3214509 2026-10-13 (merge of deliver/C3/Sheaf.CategoryTheory.GrothendieckDerivedCompactSource)
