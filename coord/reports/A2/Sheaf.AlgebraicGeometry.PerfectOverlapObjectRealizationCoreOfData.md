## What changed

The assigned item is a zero-hole rework. A4's import restoration had already landed
before this claim; the current source compiles cleanly in 16.8 seconds. Preserve it.
Replace the private irreducible equality-choice cache with the identity construction
and prove its equality reflexively, removing existsPinned. The public proposition,
theorem signature, theorem proof, imports and settings are unchanged.

Restore its unclaimed quarantined direct consumer
Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData. Redirect the obsolete
Sheaf CoreBase and PerfectHomTransport imports to the adopted source modules, remove
the extra hstage application from its Prop-valued conclusion, and retain the hstage
binder and complete canonical-family packaging proof. Remove three unused private
proof imports. The repaired set compiles through lcompile.py: CoreOfData 18.0 seconds,
CoreData 3.7 seconds before removing those unused private imports.

Update the assigned node's cache description, and the CoreData node's Lean signature
and proof dependencies to match its actual proof. Correct the data-at and data-family
node attachments to the existing CanonicalFamily module; preserve both declarations.
Change record: coord/changes/A2-perfect-overlap-core-construction-and-consumer.md.

## Proved and sorry left

Original holes in assigned item: 0. Holes closed: none. Holes added: none.
Remaining holes in the assigned item and restored consumer: none. This is a concrete
construction simplification and consumer restoration repair, not a new mathematical
proof or a decomposition. No new intermediate theorems or modules are introduced.

The complete proofs of
AlgebraicGeometry.perfect_overlap_object_realization_core_of_data and
AlgebraicGeometry.perfect_overlap_object_realization_core_data are retained.
All private helpers are proved; no definition contains sorry or chooses data from
an unproved existence theorem.

## No longer needed

Remove the assigned item's private existsPinned helper and its Classical.choose
cache implementation. The irreducible identity cache retains the same equality API.
No import or mathematical proof dependency is removed from that item.

Remove CoreData's unused private imports:

- Sheaf.AlgebraicGeometry.DerivedPullbackComposition;
- WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram;
- WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent.

Replace its obsolete public Sheaf CoreBase and PerfectHomTransport imports with
WeilConjectures CoreBase and PerfectHomTransportExtension. These redirects do not
remove the underlying mathematics.

CoreData directly uses the canonical family construction from the data-at module
and the core-of-data theorem. Its old direct proof dependencies on
lem-pc-perfect-overlap-object-realization-core-data-family,
def-pc-derived-open-restriction-maps,
def-pc-perfect-overlap-hom-continuity-data,
def-pc-perfect-overlap-stage-equivalence,
def-pc-two-open-comparison-diagram,
lem-pc-perfect-hom-transport, and
lem-pc-ringed-spaces-derived-pullback-composition are unnecessary as separate steps
of this packaging proof. The geometric dependencies remain in its statement and in
the fieldwise core-of-data proof. The family theorem remains in CanonicalFamily;
no declaration, module, unit step or DAG node is withdrawn. Modules pruned: none.

## Where the brief, the DAG or earlier work was wrong

The rework listing is older than A4's landed restoration; the assigned module already
has zero holes and compiles. This packet does not claim that restoration as new work.
The parent archive still combines the old Sheaf CoreBase with the adopted source
base and, after fixing imports, applies an already Prop-valued conclusion to hstage.
Both failures were reproduced through lcompile.py. Removing that obsolete application
repairs typing while preserving the intended core and every theorem hypothesis.

The CoreData node described the lower-level fieldwise geometry as if its own
packaging proof repeated it, and named an arbitrary family existence theorem although
the Lean proof uses the explicit canonical family. Its two single-stage/family node
attachments still named CoreData although the declarations live in CanonicalFamily.
These records now agree with the source. The assigned node's obsolete note that a
component identity remains unfinished is corrected; that dependency is fully proved.

LeanFinder and Loogle found only generic pullback-comparison and Iso.homCongr APIs;
Mathlib grep found no overlap-specific core constructor. Keep the original complete
geometric proof and the unit route. No source-library file or target is changed.

The next quarantined parent, PerfectOverlapObjectRealization, compiles as a scratch
consumer in 15.5 seconds against the repaired set after redirecting only its retired
PerfectHomTransport import. Its hstage argument and entire theorem proof are
unchanged. The scratch file is outside the delivered lean/ tree. Explicit axiom
probes for the item theorem, restored CoreData theorem and next parent theorem all
report exactly propext, Classical.choice and Quot.sound.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
