# CategoryTheory.DecreasingFiltration.cohomologyImage_graded_normalized

## Reason

The assigned queue entry is a listed retirement in `coord/retire-items.tsv`.
The Sheaf module duplicates the proved theorem in
`WeilConjectures.CategoryTheory.FilteredCohomologyImageNormalized`. Comparing the
complete theorem, from its signature through its proof, gives identical text
modulo whitespace. Its upstream proof uses only `propext`, `Classical.choice`,
and `Quot.sound`, as verified by a server compilation with `#print axioms`.

## Old

`Sheaf.CategoryTheory.FilteredCohomologyImageNormalized` declared
`CategoryTheory.DecreasingFiltration.cohomologyImage_graded_normalized`.
Its direct consumer had this proof import:

```lean
import Sheaf.CategoryTheory.FilteredCohomologyImageNormalized
```

The node `lem-sp-filtered-cohomology-image-normalized-quotient` attached the
statement to that Sheaf module.

## New

Withdraw `lean/Sheaf/CategoryTheory/FilteredCohomologyImageNormalized.lean`
through `deleted.txt`, and use the existing upstream theorem as the sole provider.
The direct consumer instead has this proof import:

```lean
import WeilConjectures.CategoryTheory.FilteredCohomologyImageNormalized
```

The node's `lean` attachment points to the upstream module and file, with the
same declaration and verbatim statement. Its mathematical statement, proof,
proof dependencies, and unit route remain valid. The theorem has no `sorry`.
The upstream file, its public imports, signature and complete proof are retained.
No definition or target statement changes, so no target statement review reopens.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FilteredCohomologyImagePresentation | unclaimed | Replace the single proof import; theorem signature and proof unchanged. |
| Sheaf.CategoryTheory.FilteredStableSubquotient | unclaimed | Indirect consumer; no source changes needed. |

`tools/downstream.py` lists these two downstream modules. A search of all active
and quarantined Lean modules found only Presentation importing the withdrawn
module. Its adapted source compiles on the server. All its other imports already
come from the upstream family, so the migration introduces no parallel Sheaf
copies of the normalized quotient, cycle map, filtration, or subquotient APIs.
The earlier `PROOFDIFF_UNSAFE` inventory predates those dependency retirements.
The DAG's parent nodes continue to use the same normalized quotient node; it is
reattached rather than removed. No unit statement or proof step is bypassed.

## Status

landed 20261021T020139-L-2590869 2026-10-21 (merge of deliver/T2/Sheaf.CategoryTheory.FilteredCohomologyImageNormalized)
