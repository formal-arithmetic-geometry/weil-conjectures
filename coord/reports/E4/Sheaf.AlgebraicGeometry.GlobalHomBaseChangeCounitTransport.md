## What changed

Restored lean/Sheaf/AlgebraicGeometry/GlobalHomBaseChangeCounitTransport.lean from
its assigned quarantine archive. The rework entry records that this importer was
rolled back with other modules and did not itself fail the batch.

The archive fails against the current adopted direct-image comparison: the rewrite
in directImage_naturality expects schemeGlobalSectionsDirectImageIso, whereas
schemeGlobalHomDirectImageMap unfolds to mixedGlobalSectionsDirectImageIso.
Use the latter in the inverse Leray naturality equation and its final whiskering.
These are the only two Lean changes relative to the archive. All public and private
signatures, public imports, definitions, options, and docstrings are preserved.
The existing node retains its Lean attachment and all dependencies, with its first
proof step documenting the compatibility repair. Change record:
coord/changes/E4-global-hom-counit-transport-restoration.md.

The complete module compiled without warnings through lcompile.py in 32.8 seconds.
A byte-for-byte check confirms the public theorem signature equals both the archive
and node record. No active consumer exists; the archived FlatPrecomposePus consumer
still calls the original theorem with its original arguments. The downstream tool
reports an unknown module because the assigned source is currently quarantined.

## Proved and sorry left

Restored the complete proof of
AlgebraicGeometry.schemeGlobalHom_baseChange_counit_transport
(lem-sc-global-hom-base-change-counit-transport), together with its four proved
private helpers homMap_comp, pullbackMate_naturality, directImage_naturality, and
pullback_naturality. Zero holes in the archive; zero holes in the delivered module.
Holes closed: none. Holes added: none. Split off: none. This is a restoration and
compatibility repair, not a new hole closure.

## No longer needed

None. Both imports are used: GlobalHomPullbackComparison supplies statement data,
and the proof-only GlobalHomBaseChangeExchange supplies the exchange equation.
All existing statement and proof dependencies remain needed. No module is withdrawn
and the quarantine archive remains untouched. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The item has no current lean/ source and zero archived sorries; coord/rework.tsv
correctly requests restoration. The only obsolete proof detail was the Leray name
in the direct-image naturality helper after upstream adoption. No mathematical
statement or definition needs correction.

Searches of Mathlib with LeanFinder, Loogle, and grep found generic adjunction
naturality, not a more direct scheme theorem. Source inspection also found the
mixed-universe counit transport theorem; applying it would require identifying
both wrapper comparisons. Restoring the existing direct argument instead requires
only the two local proof edits above and keeps the recorded route unchanged.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
