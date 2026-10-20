# CategoryTheory.pointSystemRefine

## Reason

The proof uses representatives, eventual equality, and a finite common upper bound.
It does not use the general filtered-colimit/finite-limit comparison. Replace that
public import by the smaller types-colimit module required by the unchanged statement.
The filtered types-colimit API is imported privately for the proof.
The repair also removes the unused warning-suppression option whose name was
misidentified as an unattributed hole by the landing scanner.

## Old

```lean
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
```

## New

```lean
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
```

All existing declaration signatures and visibility remain unchanged. The new index,
diagrams, instances and proof helpers are private. No definition used by a target changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PointSystemRefine | M3 | One theorem proved; imports narrowed. |
| Sheaf.CategoryTheory.PointSystemRefineAll | K3 | Unchanged; direct private importer, compiled against this delivery. |
| Sheaf.Paper.FinitarySiteEnoughPoints | J4 | Unchanged; only a transitive private import path. |
| Sheaf.CategoryTheory.Sites.FinitarySliceEnoughPoints | H3 | Unchanged; only a transitive private import path. |
| Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints | G4 | Unchanged; only a transitive private import path. |

The direct importer privately imports PointSystemRefine and separately imports
Mathlib.CategoryTheory.Limits.Types.Filtered. It does not mention pointSystemRefine
in its unfinished proof yet. No consumer needs adaptation. The four downstream modules
are the complete output of tools/downstream.py for this module.

## Status

landed 20261020T174823-L-803178 2026-10-20 (merge of deliver/M3/Sheaf.Paper.PointSystemRefine)
