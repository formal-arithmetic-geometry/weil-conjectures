# CategoryTheory.brownTelescopeAssembly

## Reason

The upstream-sync rework row preserves this module at
`quarantine/Sheaf/CategoryTheory/BrownTelescopeAssembly.lean`.
Its public import of the duplicate compact-object module collided with
`WeilConjectures.CategoryTheory.CompactObject`, imported by the telescope comparison.
The later K9 retirement withdrew the duplicate without a compatibility re-export.
Compiling the archived source now reports that `IsCompactObject` exists only through a
private import. Restore the archived module and directly re-export the canonical source.

## Old

```lean
public import Sheaf.CategoryTheory.CompactObject
```

## New

```lean
public import WeilConjectures.CategoryTheory.CompactObject
```

The rest of the archived file is byte-for-byte unchanged. In particular the theorem's
signature, visibility, docstring, complete proof, private shift lemma, and proof imports
are preserved. The canonical compactness definition has the same name, universes and
body as the retired duplicate. No definition or target statement changes.
The node `lem-pc-brown-telescope-assembly` keeps its existing Lean attachment and all
statement and proof dependencies; no DAG route changes.

## Users

A source scan of `lean/` finds no live importer of the quarantined module.
The only direct archived importer is listed below. Other archived descendants remain
assigned to their own rework rows; none imports this module directly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.BrownTelescopeAssembly | Q4 | Restore with canonical public import. |
| Sheaf.CategoryTheory.BrownRepresentabilityConstruction | unclaimed, quarantined | Same theorem name and elaborated type; its private application is unchanged. Its own retired public compactness import needs its own rework repair. |

Validation: archived source fails with the private-import error; repaired source compiles
cleanly in 1.7 seconds. An axiom probe of `CategoryTheory.brownTelescopeAssembly` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Status

landed 20261020T150701-L-2573280 2026-10-20 (merge of deliver/Q4/Sheaf.CategoryTheory.BrownTelescopeAssembly)
