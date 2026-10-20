## What changed

Restored Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh from its quarantine assignment
as a public re-export of WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCoh.
The complete adopted affine-cover proof supplies the same fully qualified theorem.
This removes the duplicate derived-pullback environment and duplicate theorem risk.
The node retains its attachment and proof dependencies; its Lean signature now records
IsKFlatTensor, the identical-body upstream spelling of IsAcyclicTensorKFlat.
Change record: coord/changes/R3-derived-pullback-tensor-qcoh-reexport.md.

The restored module compiled through lcompile.py. A scratch server check restates the
whole archived conjunction using the exact former K-flat definition body and proves
it by applying the adopted theorem; it compiles. #print axioms lists only propext,
Classical.choice, Quot.sound. Source signatures compare identically after the sole
predicate rename. The direct archived consumer calls all select the unchanged first
conjunct; no consumer edit is required.

## Proved and sorry left

Assigned repair, zero initial sorries and zero final sorries. Holes closed: none (0 of 0).
Holes added: none. Split off: none.
AlgebraicGeometry.derivedPullback_tensor_preserve_QCoh remains fully proved by the
adopted source theorem. This is an interface repair, not a new proof or decomposition.

## No longer needed

Removed direct imports Sheaf.AlgebraicGeometry.DerivedPullback,
Sheaf.Algebra.Homology.KFlat,
WeilConjectures.AlgebraicGeometry.DerivedPullbackPreservesQCoh, and
Sheaf.AlgebraicGeometry.DerivedTensorPreservesQCoh from the archived module.
The first and last Sheaf twins are already withdrawn stubs; the adopted theorem
uses the canonical upstream definitions and affine component theorems instead.
The local duplicate theorem and its local monoidal instance are unnecessary because
the source module provides the public theorem.
No mathematical node or proof dependency is pruned: both
lem-pc-derived-pullback-qcoh-component and lem-pc-derived-tensor-qcoh-component are still
used by the adopted proof. No module is withdrawn by this delivery.

## Where the brief, the DAG or earlier work was wrong

The quarantine is an upstream-interface synchronization problem, not an unfinished
mathematical proof. The archived module already had zero holes. The adopted source
contains the same theorem, with the renamed but identical K-flat predicate. The Lean
record used the obsolete spelling and is refreshed without changing its mathematical
statement or its affine-local route. The repository downstream tool cannot index the
absent quarantined source, so direct importers were checked by searching quarantine
as well as lean. There are five, all using the unchanged pullback conjunct.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
