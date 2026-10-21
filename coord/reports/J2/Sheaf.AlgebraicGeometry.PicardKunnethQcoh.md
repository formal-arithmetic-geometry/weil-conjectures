## What changed

Restored Sheaf.AlgebraicGeometry.PicardKunnethQcoh from its recorded quarantine
archive. Replaced only the obsolete public Sheaf scalar-operations import with
WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations.
The complete archived proof, both conjuncts of the statement, visibility and
remaining imports are unchanged. Preserved the node attachment and dependencies;
added only an explanatory lean.note.

The original archive fails compilation because Scheme.Modules is only privately
available. The repaired source compiles cleanly in 3.3 seconds. A separate public-import
probe compiles in 2.8 seconds, confirming the theorem and scalar operations are
exported; the axiom print reports propext, Classical.choice, Quot.sound and
inherited sorryAx from existing dependencies. The probe is removed from the packet. The two existing
proof dependencies have exactly the required isomorphism and functoriality clauses.
The source statement and canonical cup map were checked against Stacks Varieties,
lemma-kunneth, Tag 0BED. No mathematical change or forced adaptation is made.

Change record: coord/changes/J2-picard-kunneth-qcoh-restoration.md.

## Proved and sorry left

Zero of zero local holes closed. Zero holes added or split off; zero local holes
remain. AlgebraicGeometry.Scheme.Modules.picard_kunneth_qcoh has its complete
existing conjunction proof from picard_kunneth_iso_exists and
picard_kunneth_functoriality (node lem-sc-picard-kunneth-qcoh).
This is a quarantine/import repair, not a new mathematical proof. Inherited
unfinished results below the two existing dependencies are retained.

## No longer needed

Removed the public import of the withdrawn empty module
Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations and replaced it
with its canonical upstream counterpart. Both private proof imports are needed
and retained. No mathematical node or dependency is pruned; no module or
attachment is withdrawn. There are no current Lean importers, but the actual
DAG parent lem-sc-picard-h1-product-spanning still cites this item and is preserved.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined rather than present under lean/; its exact archive
has zero local holes and a complete proof. Its public scalar-operations import
became obsolete after migration to WeilConjectures. Restoration with the canonical
import repairs that concrete failure. The current DAG proof is already the two
conjuncts, and is accurate; no route or statement repair is necessary.

LeanFinder returned pullback/free-sheaf comparison results, not this Kunneth
statement. Loogle has no externalCup identifier; grep and direct library searches
found no replacement for the two existing dependencies. The existing short
conjunction proof remains the appropriate route.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
