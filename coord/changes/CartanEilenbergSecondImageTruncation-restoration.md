# CartanEilenbergSecondImageTruncation imports

## Reason

Restore the quarantined item assigned in `coord/rework.tsv`. Its archived proof
has zero holes, but its direct import of the old Sheaf double-complex module
collides with the upstream declarations now publicly imported by
`WeilConjectures.CategoryTheory.CartanEilenbergPresentation`.
The original compiler error is:

```
import Sheaf.CategoryTheory.DoubleComplexTotal failed, environment already contains
'HomologicalComplex₂.secondFiltration_graded' from
WeilConjectures.CategoryTheory.DoubleComplexTotal
```

Remove the obsolete private import. The existing public presentation import
already supplies the complete double-complex interface. The theorem statement,
proof, public imports, visibility, definitions and attributes stay verbatim.
No target meaning changes and no definition-based target review is needed.

## Old

```lean
import Sheaf.CategoryTheory.DoubleComplexTotal
```

## New

The above private import is removed, with no replacement import.

## Users

`tools/downstream.py` cannot index the absent quarantined module (it prints
`unknown module(s)`). A full source search of `lean/Sheaf`, `lean/WeilConjectures`
and `quarantine` finds exactly one importer and user, listed below. DAG search
also confirms that `lem-sp-ce-acyclic-abutment` still needs the item in its proof.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment | quarantined; no local claim | Unchanged theorem interface; original archived consumer checked in a scratch overlay. |

This is a private-import repair; no consumer adaptation is required. No source
library file is changed. The item's node attachment, dependencies and three-step
proof route are preserved. The obsolete duplicate Sheaf module is not withdrawn.

## Status

landed 20261021T004828-L-1791969 2026-10-21 (merge of deliver/E4/Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation)
