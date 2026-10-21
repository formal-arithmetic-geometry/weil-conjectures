## What changed

Restored Sheaf.AlgebraicGeometry.PicardDirectImageSectionMap from its preserved
quarantine source, as assigned by coord/rework.tsv. The full Lean file is byte for
byte identical to the archive: the canonical additive section map, shared derived
categories, signature, body, five public imports and docstrings are preserved.
The source is absent from the live library, so this repairs a missing construction
and restores its named declaration rather than submitting a compiling no-op.

Updated only the existing node's lean.by, lean.date and restoration note. The
statement, proof plan, dependencies, attachment and unit route are unchanged.
The change record is
coord/changes/N4-picard-direct-image-section-map-restoration.md.

The restored file compiled cleanly through lcompile.py in 20.8 seconds. LeanFinder,
Loogle and grep found ingredients, but no replacement for this exact canonical map.
A source scan across lean/ and quarantine/ found three direct public importers and
23 transitive importers; the change record lists each. All retain exactly the same
archived definition and public environment. None needs adaptation for this restore.

## Proved and sorry left

This is a zero-hole restoration. The restored definition
AlgebraicGeometry.Scheme.picardDirectImageSectionMap has complete map_zero' and
map_add' proofs and no sorry. Its node is def-sc-picard-direct-image-section-map.
Holes closed: 0 of 0. Holes added: 0. Holes left in the delivered module: 0.
No new theorem, definition, axiom or split-off lemma is introduced.

## No longer needed

None. No import, declaration, module or DAG dependency is removed or pruned.
All five archived public imports remain verbatim. The quarantined consumers and
their DAG edges remain needed and are preserved for their own rework assignments.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 proof brief describes an open sorry, but the current rework
entry is a missing zero-hole definition. The archive already compiles against the
current interfaces; no additional mathematical or elaboration defect was found.
The required repair is to restore that complete canonical construction. The
missing live source is not evidence of withdrawal. tools/downstream.py cannot
inspect the absent live module, so the consumer check uses the source union of
lean/ and quarantine/ instead. No tool workaround or tool modification was used.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
