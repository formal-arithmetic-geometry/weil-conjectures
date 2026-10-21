# CategoryTheory.DecreasingFiltration.cohomologyImage_cycle_map

## Reason

The assigned queue entry is a listed retirement. The Sheaf module duplicates the
complete theorem in the adopted upstream module
`WeilConjectures.CategoryTheory.FilteredCohomologyImageCycleMap`. The upstream
theorem has the same declaration name, signature, docstring mathematics, and
permitted-axiom proof. Withdraw the duplicate and migrate its direct consumer to
the canonical provider. No source-library file or target statement is changed.

## Old

The Sheaf module `Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap` provided
`CategoryTheory.DecreasingFiltration.cohomologyImage_cycle_map` and imported the
Sheaf compatibility module plus the two proof-helper modules. Its direct consumer
had this proof import:

```lean
import Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap
```

## New

Withdraw `lean/Sheaf/CategoryTheory/FilteredCohomologyImageCycleMap.lean` using
`deleted.txt`. The existing theorem in
`WeilConjectures.CategoryTheory.FilteredCohomologyImageCycleMap` remains the sole
provider. The direct consumer instead imports:

```lean
import WeilConjectures.CategoryTheory.FilteredCohomologyImageCycleMap
```

The DAG node `new-cohomology-image-cycle-map` is reattached to the existing
upstream declaration and file. Its mathematical statement and proof dependencies
are unchanged. The upstream theorem's proof compiles with only
`propext`, `Classical.choice`, and `Quot.sound`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredCohomologyImageNormalized | unclaimed | Change one proof import to the upstream module. |
| Sheaf.CategoryTheory.FilteredCohomologyImagePresentation | unclaimed | No direct edit; it reaches the theorem through Normalized. |
| Sheaf.CategoryTheory.FilteredStableSubquotient | unclaimed | No direct edit; it reaches the theorem through Presentation. |

A repository-wide import search found no other active or quarantined direct
importer. The upstream declaration is retained verbatim.

## Status

landed 20261021T013346-L-2290175 2026-10-21 (merge of deliver/K2/Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap)
