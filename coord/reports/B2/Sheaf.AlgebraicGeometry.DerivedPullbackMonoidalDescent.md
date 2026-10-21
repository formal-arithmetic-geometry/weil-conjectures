## What changed

Repaired return C-3b01e, delivery head 3b01ec8345f. Its independent reader passed
this mathematical packet, but landing rejected a reviewer correction supplied as
a bare filename. The repaired packet explicitly includes the change record at
coord/changes/B2-derived-pullback-monoidal-descent-restoration.md and records that
reviewer corrections must use this repository-relative path.

Reconciled the retained delivery with current sheaf-dag: the model compatibility
consumer is byte-identical to the current module. The two retained nodes change
only their Lean attachments to the existing adopted source declarations. Their
statements, proof plans, dependencies, audit fields and unit route are preserved.
The prescribed delivery tool constructs the commit on freshly fetched sheaf-dag.

The approved retirement remains in deleted.txt for
Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent. Its replacement is the
existing source theorem, and the consumer uses the adopted source model.
The source-library declarations and quarantine archives are preserved.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. No sorry remains in any Lean
file of this packet. This delivery completes the assigned duplicate retirement
and repairs the returned delivery metadata; it claims no new mathematical proof.

The existing replacement declarations are
AlgebraicGeometry.derivedPullback_monoidal_descent,
AlgebraicGeometry.IsDerivedPullbackMonoidalModel, and
AlgebraicGeometry.exists_derivedPullbackMonoidalModel.
The delivered compatibility consumer compiled on the server with lcompile.py in
4.7 seconds, with exit code 0 and no compiler messages. A fresh server probe
compiled in 1.8 seconds and printed only propext, Classical.choice and Quot.sound
for each of the three replacement declarations above.

## No longer needed

Retired duplicate module: Sheaf.AlgebraicGeometry.DerivedPullbackMonoidalDescent.
Its DAG node now names the adopted source module and the same theorem. The
compatibility consumer imports
WeilConjectures.AlgebraicGeometry.DerivedPullbackMonoidalModel, which imports the
adopted descent and tensor-product modules. The former duplicate model
and descent declarations are supplied by their existing source counterparts.

The archived consumer's imports of the Sheaf descent and tensor-product twins
are unnecessary in the current compatibility consumer. No mathematical node,
proof dependency, parent edge or unit step is pruned. The descent's three proof
dependencies and the model's three proof dependencies remain intact.

## Where the brief, the DAG or earlier work was wrong

The latest return is a failed landing after a passed review, not a request to
change the mathematical proof. The rejected correction lacked the directory
prefix of its change record. This packet includes the record at the exact
coord/changes path and documents that path for the independent reader.

Unlike the older retained report, current sheaf-dag contains compatibility
modules at both former Sheaf paths. The explicit retirement row still identifies
the source descent as the replacement. This authorizes retirement of the twin;
it is not inferred from zero importers or an absent quarantine path. No archive
is deleted and no upstream declaration is removed or weakened.

The adopted name CochainComplex.IsKFlatTensor is the acyclic-tensor predicate
formerly named IsAcyclicTensorKFlat at the twin path. The node attachments record
the actual source signatures. No target, launcher script or check was changed.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
