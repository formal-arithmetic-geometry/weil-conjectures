## What changed

Restored lean/Sheaf/AlgebraicGeometry/NewBaseOpenMateFactorization.lean from the
quarantine path recorded in coord/rework.tsv. Replaced its private proof import
of Sheaf.AlgebraicGeometry.DerivedPullbackComposition with the current
WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition. The latter provides
exists_derivedPullbackComposition, as recorded by the existing dependency node.
Removed a redundant blank line. The theorem signature, complete proof, public
imports and options are preserved. The quarantine archive is untouched.

The restored module compiles through lcompile.py in 7.0 seconds. The proof uses
horizontal_duality_mate_pasting, proves q followed by pullback associativity is r,
and transports the pasting arrow isomorphism using naturality of delta and the
derived composition comparison. Neither a mate nor delta is required to be a
canonical chosen isomorphism. The argument also applies to empty opens and zero
objects without additional assumptions.

Change record: coord/changes/V3-new-base-open-mate-factorization-restoration.md.

## Proved and sorry left

AlgebraicGeometry.newBase_open_mate_factorization has a complete existing proof,
now restored and compiling against the current upstream interfaces.
The archive had zero holes; the delivered module has zero holes. Holes closed:
none (0). Holes added: none (0). No statements were split off. This is an assigned
quarantine/import repair, not a newly closed proof hole. No sorry is left in any
delivered Lean file. Imported dependencies retain their existing proof status.

## No longer needed

Removed the private import Sheaf.AlgebraicGeometry.DerivedPullbackComposition,
which is an empty withdrawn wrapper. Its upstream replacement is required and
is imported privately. No mathematical dependency node is pruned: both
lem-sc-horizontal-duality-mate-pasting and
lem-pc-ringed-spaces-derived-pullback-composition are used. The item's existing
DAG node and Lean attachment remain intact. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The live item source is absent because it was quarantined, not because its
statement was withdrawn. Its rework row reports the upstream duplicate-derivedPullback
import failure. The archived proof already has zero sorry; its remaining stale
Sheaf composition import must point to the adopted upstream provider after sync.
The current DAG already records that provider, so no node edit is necessary.
There is no additional V3 return entry. No definition repair or signature change
was needed. Source searches include the quarantined RightAdjointMateNewBaseOpen
parent: its call still matches the restored theorem verbatim. No live consumer
was found by downstream.py. No consumer adaptation is forced by this import-only
repair, and the unit route is preserved.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
