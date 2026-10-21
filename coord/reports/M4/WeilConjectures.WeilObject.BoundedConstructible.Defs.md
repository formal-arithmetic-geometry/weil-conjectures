## What changed

Restored `lean/WeilConjectures/WeilObject/BoundedConstructible/Defs.lean`
from the exact quarantine path recorded in `coord/rework.tsv`. The current
library path was absent following the merge-queue cluster rollback. This is
a source restoration, not a proof-count reduction or withdrawal.

The file is byte-for-byte identical to the archive. It restores
`AlgebraicGeometry.ProEtale.CondensedRing.WeilBoundedConstructible` and its
`forget`, `toDerivedCategory`, and `toDerivedCategory_obj_carrier` declarations,
with all original public imports, signatures, attributes and bodies intact.
The category is the IsoAlgebra of the restricted derived pullback. Transport
along the inclusion uses the inverse compatibility isomorphism, of the exact
type required by `IsoAlgebra.mapOfNatIso`; the carrier equation is `rfl`.
No arbitrary object is chosen from an existence theorem.

The restored module compiled on the project server in 5.6 seconds with no
errors or warnings. The source contains zero holes. The delivery tool supplies
the final compile and axiom probes.

The restoration and consumer inventory are documented in
`coord/changes/M4-weil-bounded-constructible-defs-restoration.md`.
No current node has this module as its `lean.module` (checked all node records),
so no existing node attachment, dependency, proof or unit route is changed.
The coefficient and bounded-constructible nodes continue to use their recorded
interfaces. The quarantine archive itself remains untouched.

## Proved and sorry left

Original archived holes: 0. Restored holes: 0. Holes closed: none. Holes added:
none. Split off: none. The existing complete proof
`AlgebraicGeometry.ProEtale.CondensedRing.WeilBoundedConstructible.toDerivedCategory_obj_carrier`
is preserved. The two functors and the category abbreviation are real
constructions with no `sorry` in their data.

## No longer needed

None. All three original public imports are preserved. No node, declaration,
module or dependency is pruned, deleted or withdrawn. The three quarantined
consumer modules remain needed and are not part of this delivery.

The requested short-route searches were performed with LeanFinder, Loogle
and Mathlib grep, and the source-library API was inspected. The source already
uses its generic `IsoAlgebra.mapOfNatIso` construction; no replacement or
new auxiliary declaration is required.

## Where the brief, the DAG or earlier work was wrong

This assigned item has zero archived holes and is a rework restoration:
`coord/rework.tsv` says it was reverted by the merge queue after a cluster
restore. Its absence does not authorize withdrawal. No mathematical defect
was found in its definitions. The archived source compiles unchanged.

The ordinary downstream command initially rejects an absent module; its
supported `--allow-missing` option reports zero current importers. Import-line
searches over both the library and quarantine identify the three quarantined
consumers listed in the change record. No consumer source is adapted.

Consumer verification against the restored module: `LowerUpperShriek` compiled
unchanged in 7.4 seconds. `TensorHom` exceeded the single-file 60-second limit,
so this optional consumer check is inconclusive; that quarantined module is
neither modified nor delivered. This repair restores the exact archived
interface, and does not change any definition used by its proofs.

`UpperLowerStar` also compiled unchanged in 4.3 seconds. Verification copies
were removed from the packet; only the assigned module is delivered.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
