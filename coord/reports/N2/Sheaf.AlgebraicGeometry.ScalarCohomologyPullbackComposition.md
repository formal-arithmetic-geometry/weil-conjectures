## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ScalarCohomologyPullbackComposition.lean`
from its rework quarantine. Replaced its public scalar-operation import and its
private Ext comparison import by their canonical upstream modules. Removed the
unused private `WeilConjectures.AlgebraicGeometry.TensorPullback` import.
The theorem `AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_comp`
retains its exact archived signature, docstring, and complete proof.

The restored file compiles cleanly using `lcompile.py` (9.7 seconds). A separate
importing probe also compiles (module 6.9 seconds, probe 1.3 seconds);
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`,
with no transitive `sorry` dependency. Its proof
applies coefficient naturality, inverse-image composition coherence, and the
exact-functor comparison, then reassociates the degree-zero Ext factors.
Change record: `coord/changes/scalarCohomologyPullbackComposition-upstream-imports.md`.

## Proved and sorry left

This is a zero-hole import repair: 0 holes closed out of 0, 0 holes added,
0 split off, and no `sorry` remains in the delivered module.
`AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_comp` has its existing
complete proof restored against upstream dependencies. No proof is replaced by
a new assumption.

## No longer needed

Removed imports:
- `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`: duplicate of
  the adopted upstream scalar operations, now imported publicly instead.
- `Sheaf.CategoryTheory.ExtExactFunctorCompositionComparison`: duplicate of the
  adopted upstream Ext comparison, now imported privately instead.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`: the proof does not use its
  nonempty comparison theorems; the normalized comparison and tensor API are
  already available from the public scalar operations import.

No DAG dependency or mathematical result is pruned: the same scalar operations,
coefficient naturality, inverse-image coherence, and Ext comparison are used.
No module is withdrawn. The item's Lean attachment and the archived parents are
preserved. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined import repair with zero textual holes, rather than an
unfinished composition proof. The rework row correctly identifies a duplicate
scalar-operation environment after upstream sync. Two recorded dependency
attachments still name the local copies, whereas the upstream library already
provides their identical public API. This delivery selects the canonical copies
without altering those dependencies or their definitions.

Fresh searches: LeanFinder returned generic module-pullback composition lemmas;
Loogle returned exact-functor Ext algebra; msearch grep returned no scalar
composition match. Local searches found the existing upstream coherence and Ext
comparison needed by the retained proof, and no duplicate composition theorem.
The three separate quarantined square and Kunneth consumers retain their assigned
sync repairs; no active consumer is changed by this packet.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
