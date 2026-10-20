## What changed

Restored `lean/Sheaf/CategoryTheory/CohomologicalGeneratorDetection.lean` from its
quarantine archive, preserving the complete proof and theorem interface. Replaced
its public import of `Sheaf.CategoryTheory.CompactObject` with
`WeilConjectures.CategoryTheory.CompactObject`, the canonical owner of
`CategoryTheory.IsCompactObject` already used by `compactGenerators_buildObjects`.
This repairs the duplicate-declaration import failure recorded in `coord/rework.tsv`.

Change record:
`coord/changes/cohomological-generator-detection-canonical-compact-import.md`.
No adopted source-library file, consumer, target, definition or statement is changed.
The existing DAG attachment, dependencies, proof route and unit route are preserved.
The archived Brown consumer was read and still applies the identical theorem type.
`tools/downstream.py --allow-missing --uses cohomologicalGeneratorDetection` reports
zero live downstream modules; a separate search of both `lean/` and `quarantine/`
found the archived Brown module as the sole consumer.

Single-file compilation through `lcompile.py` passed without warnings (1.9 seconds).
An additional compile with `#print axioms CategoryTheory.cohomologicalGeneratorDetection`
reported exactly `propext`, `Classical.choice`, and `Quot.sound` (2.0 seconds).
The diagnostic command was then removed from the delivered file.

## Proved and sorry left

This is a zero-hole quarantine repair. The archived module already proved
`CategoryTheory.cohomologicalGeneratorDetection`
(node `lem-pc-cohomological-generator-detection`); its proof is retained verbatim.
Original holes: 0. Holes closed in this session: 0. Holes added: 0. Holes left: 0.
Split off: 0. No declaration in the delivery contains `sorry`, and the theorem's
transitive proof now uses only the three permitted axioms.

## No longer needed

Removed the obsolete public import of `Sheaf.CategoryTheory.CompactObject` from this
module and replaced it with the canonical upstream import. The retired Sheaf module
is already empty; this delivery neither withdraws nor prunes any module or DAG node.
Every other import is retained: the generating-family signature, homological Yoneda
instance, compact-generator construction, five lemma and preservation of Yoneda
limits are all used by the unchanged proof. No mathematical dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The dispatched generic proof brief describes a possible sorry-bearing module, but
this item is the listed zero-hole rework at the quarantine path. Its actual defect
was the obsolete compact-object import following canonical upstream migration.
The archived mathematical proof and the node's three-step plan remain valid; the
restored proof compiles unchanged against the current canonical definitions.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
