## What changed

Restored WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive
from its quarantined source, verbatim. The assigned rework row identifies a merge-queue
rollback after a cluster restore; the missing file is not a withdrawn mathematical result.
The restoration reinstates its four original public instances and both public imports.
No proof, signature, attribute, definition, or public import differs from the archive.

The first two proofs restrict additive ambient functors to full subcategories. The third
uses additivity of the composite defining the compactification lower shriek; the fourth
specializes that construction to the chosen compactification. Existing generic instances
already discharge all four proofs, so no new helper or dependency is necessary.

Change record: coord/changes/R4-bounded-constructible-additive-restoration.md.

## Proved and sorry left

This is a source-restoration repair with zero original textual sorries and zero remaining
textual sorries. Holes closed: none. Holes added: none. Split off: none.

The four restored, already-proved declarations, all in
AlgebraicGeometry.ProEtale.CondensedRing, are:

- additive_boundedConstructibleLowerStar
- additive_boundedConstructibleOpenImmersionLowerShriek
- additive_boundedConstructibleLowerShriekOfCompactification
- additive_boundedConstructibleLowerShriek

The archived source compiles against the current published dependencies in 2.5 seconds,
with exit code 0 and no diagnostics. This does not claim that inherited mathematical
obligations in the bounded-constructible preservation results have been closed.

All three unchanged downstream consumers also compile against the restored module in the
same sandbox overlay, each as a separate file: Dualizing (21.9 seconds), Correspondence
(8.8 seconds), and Main (27.8 seconds). Dualizing and Correspondence retain pre-existing
namespace/style linter warnings; the delivered item itself has no diagnostics. Temporary
consumer source copies were removed from the delivery after these checks.

## No longer needed

None. Both original public imports and every declaration are retained. No node, module,
proof dependency, or unit route is withdrawn. No new statement module is introduced.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 description mentions an item with sorries; this particular assignment
is a quarantined zero-hole restoration in coord/rework.tsv. Its original four proofs already
compile, and replacing them merely to create a diff would not repair an additional defect.
The actual repair adds the missing source module back to the live library.

No DAG node currently attaches to this module or names these four declarations; no existing
Lean attachment or dependency is removed or changed. No new mathematical claim requires a
new node. The archive remains untouched. No target statement changes.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
