# Sheaf.CategoryTheory.ColimitSiteFiniteUnitZeroDetection import visibility

## Reason

`Mathlib.CategoryTheory.Comma.Over.Basic` is used only by the proof (for the
`Under j` identity object) and is not needed by the public theorem signature.
The stage-3 proof therefore demotes it from a public import to a proof-only
import, reducing the interface seen by importers.

## Old

```lean
public import Mathlib.CategoryTheory.Comma.Over.Basic
```

## New

```lean
import Mathlib.CategoryTheory.Comma.Over.Basic
```

The theorem signature and declaration visibility are unchanged. The item and
its new structural helper are the only delivered modules; no downstream module
uses this import directly.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ColimitSiteAbelianSectionEventualEquality | unclaimed | Compiles unchanged; it independently publicly imports Mathlib.CategoryTheory.Comma.Over.Basic. |

## Status

landed 20261012T214710-L-1271191 2026-10-12 (merge of deliver/M1/Sheaf.CategoryTheory.ColimitSiteFiniteUnitZeroDetection)
