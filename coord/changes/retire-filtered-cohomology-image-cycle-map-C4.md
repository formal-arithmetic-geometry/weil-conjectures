# CategoryTheory.DecreasingFiltration.filtered-cohomology-image: retirement withdrawn

## Reason

The retirement of `Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap` in favour of its
upstream twin is withdrawn. The return of 2026-10-20 allows the Sheaf CycleMap module to stay
for now. The whole Sheaf chain stays as it is: Image, CycleMap, Normalized, Presentation and
StableSubquotient. The chain will be retired as one unit later.

The delivered switch of `Sheaf.CategoryTheory.FilteredStableSubquotient` to the upstream
`homologyFiltration` interface was not forced: the live module compiles against this delivery.
It is therefore not part of this delivery.

## Old

No declaration, signature, import or DAG `lean` record is changed.

## New

Unchanged. The only edit is inside the proof of `cohomologyImage_cycle_map`
(`have hTZ : T ≤ Z := by exact inf_le_right`). No other module sees it.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.CategoryTheory.FilteredCohomologyImageNormalized` | unclaimed | none |
| `Sheaf.CategoryTheory.FilteredCohomologyImagePresentation` | unclaimed | none |
| `Sheaf.CategoryTheory.FilteredStableSubquotient` | unclaimed | none |
| `Sheaf.CategoryTheory.FilteredStationaryCycleComparison` | J1 | none |

## Status
landed 20261021T001111-L-1371181 2026-10-21 (merge of deliver/C4/Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap)
