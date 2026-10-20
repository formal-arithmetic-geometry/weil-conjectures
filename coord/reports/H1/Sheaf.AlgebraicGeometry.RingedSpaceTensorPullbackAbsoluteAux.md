## What changed

Restored the quarantined item as a compatibility module publicly importing
WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsoluteAux. The source
implementation already proves both public theorems using the same resolving-class
argument. Reusing it removes the recorded collision between the old Sheaf and
adopted WeilConjectures tensor-pullback declarations. The archive is preserved;
there is no deleted.txt and no upstream file is edited.

Reattached q3-ringed-space-tensor-pullback-left-derived and
q3-ringed-space-tensor-pullback-absolute-postcomposition to their canonical source
module and quoted signatures. The source spelling IsKFlatTensor has the same
body as the former IsAcyclicTensorKFlat. The mathematical statements, dependencies
and proof plans remain unchanged, including the unit route.

Validation: the compatibility module compiles on the project server. A separate
compile probe reconstructs the archived K-flat predicate and both full archived
theorem types and supplies each directly with the canonical theorem. Axiom probes
for both canonical declarations report only propext, Classical.choice and Quot.sound.
The probe also checks the archived parent
exists_absolute_leftDerived_tensorModulePullback with its original two-line
combining proof and imports the canonical parent
WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackAbsolute. All these
checks pass when compiled together with the repaired wrapper via lcompile.py
--all, ensuring the consumer sees the sandbox implementation.
There are zero live importers according to downstream.py --allow-missing; the
quarantine search and rework rows preserve the archived consumer inventory in the
change record. No consumer is edited or withdrawn.

Change record: coord/changes/H1-tensor-pullback-absolute-aux-upstream.md.

## Proved and sorry left

This is an assigned zero-hole import repair, not a new proof or decomposition.
Archived item: zero sorry; restored item: zero sorry. Holes closed: zero. Holes
added: zero. Split off: zero. There are no sorry declarations in this delivery.

The preserved, now re-exported proofs are:

- AlgebraicGeometry.RingedSpace.exists_tensorPullback_leftDerived
  (q3-ringed-space-tensor-pullback-left-derived).
- AlgebraicGeometry.RingedSpace.leftDerived_tensorPullback_absolute
  (q3-ringed-space-tensor-pullback-absolute-postcomposition).

Both canonical declarations are fully proved, with no sorryAx in their axioms.

## No longer needed

The duplicate local implementation and its direct imports are replaced by the
single public canonical import. Removed direct imports from the archived item:
Sheaf.Paper.DerivedHomMayerVietoris;
Sheaf.Algebra.Homology.KFlatPullback;
Mathlib.CategoryTheory.Functor.Derived.LeftDerived;
Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived;
Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso;
Mathlib.CategoryTheory.Adjunction.Additive;
WeilConjectures.AlgebraicGeometry.InverseImageTensorPullbackComparison;
WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy;
WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge;
Sheaf.Algebra.Homology.KFlatResolution;
WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated.

These mathematical dependencies remain in the canonical implementation's import
closure where needed. No DAG dependency, node or library module is withdrawn;
no global pruning count is claimed. The former private helpers are already proved
privately in the canonical module, so they need no duplicate local declarations.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving remaining holes, but this item's rework row
is a zero-hole sync repair. Merely changing KFlatPullback to its canonical import
would retain duplicate public theorem names: the complete auxiliary module has
also been adopted upstream. The correct repair is to re-export that module and
update the stale attachments, rather than reconstruct or delete its mathematics.
An initial standalone probe used the published item olean instead of the sandbox
source; compiling the wrapper and probe together corrected that test setup.
The archived consumers are still recorded and remain available for their own
sync repairs. No hypothesis, conclusion, universe or target statement is changed.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
