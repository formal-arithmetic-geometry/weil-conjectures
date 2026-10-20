# CategoryTheory.cohomologicalGeneratorDetection

## Reason

Restore the quarantined module after the upstream sync. The recorded failure in
`coord/rework.tsv` is a duplicate `CategoryTheory.IsCompactObject` environment entry:
the archived file publicly imports the retired `Sheaf.CategoryTheory.CompactObject`,
while its generator-construction dependency imports the canonical upstream module.
The retired Sheaf module now contains no declarations. Import the canonical owner
explicitly, as the adopted construction module does.

## Old

```lean
public import Sheaf.CategoryTheory.CompactObject
```

## New

```lean
public import WeilConjectures.CategoryTheory.CompactObject
```

All declarations, signatures, proofs, docstrings and remaining imports are preserved
verbatim from the quarantine archive. This is an import repair, not a definition or
statement change. No target meaning changes and no source-library module is edited.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.CohomologicalGeneratorDetection | S2 (this item) | Restored from quarantine; canonical compact-object import; compiles. |
| Sheaf.CategoryTheory.BrownCohomologicalRepresentability | unclaimed; quarantined | Archived direct consumer; same theorem name and type, now using the canonical compactness definition already imported by this consumer. No adaptation needed. |

`tools/downstream.py Sheaf.CategoryTheory.CohomologicalGeneratorDetection
--allow-missing --uses cohomologicalGeneratorDetection` reports zero live downstream
modules and zero live uses, as expected while this module is quarantined. Searches
of `lean/` and `quarantine/` found no other import or declaration-name consumer. The archived Brown consumer was read, including its application of this
theorem. The adopted upstream Brown module has a different complete proof and does
not import or use this module. No consumer is withdrawn or modified.

## Status

landed 20261020T150704-L-2573927 2026-10-20 (merge of deliver/S2/Sheaf.CategoryTheory.CohomologicalGeneratorDetection)
