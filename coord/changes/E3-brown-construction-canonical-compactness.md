# CategoryTheory.brownRepresentabilityConstruction

## Reason

Restore the assigned rework item from
`quarantine/Sheaf/CategoryTheory/BrownRepresentabilityConstruction.lean`.
Its compactness import was retired to an empty module. The archived source fails
because `IsCompactObject` is available only through a private proof import.
The canonical compactness definition is provided by the adopted source library.

## Old

```lean
public import Sheaf.CategoryTheory.CompactObject
```

## New

```lean
public import WeilConjectures.CategoryTheory.CompactObject
```

Only this import changes relative to the quarantined source. The theorem statement,
universes, visibility, docstring, complete proof and proof imports are unchanged.
No definition or target statement changes. The node
`lem-pc-brown-generator-construction` retains its existing Lean attachment, proof,
statement dependencies and proof dependencies; these still match the restored proof.

## Users

`tools/downstream.py` cannot enumerate this quarantined module: it reports
`unknown module(s)`. A source scan of both `lean/` and `quarantine/` finds exactly
one direct consumer, listed below. A scan of DAG references also retains the
unfinished parent `lem-pc-brown-cohomological-representability` and both construction
dependencies. No withdrawal or pruning of these dependencies is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.BrownRepresentabilityConstruction | E3 | Restore canonical public import. |
| Sheaf.CategoryTheory.BrownCohomologicalRepresentability | unclaimed, quarantined | Its original application retains the same statement and requires no adaptation. |

Validation: the archived source reproduces the public/private import error.
The restored source compiles cleanly. A temporary axiom probe reports only
`propext`, `Classical.choice`, and `Quot.sound`. The unmodified quarantined
consumer `Sheaf.CategoryTheory.BrownCohomologicalRepresentability` also compiles
against the restored module; its temporary test copy is excluded from the delivery.

## Status

landed 20261020T153000-L-2858448 2026-10-20 (merge of deliver/E3/Sheaf.CategoryTheory.BrownRepresentabilityConstruction)
