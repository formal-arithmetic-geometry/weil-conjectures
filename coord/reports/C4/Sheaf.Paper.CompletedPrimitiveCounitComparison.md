## What changed

Restored lean/Sheaf/Paper/CompletedPrimitiveCounitComparison.lean from the current
quarantine archive named by coord/rework.tsv. Repaired the finiteTensorBridge
functor equality: unfold unrestrictedIntegralReductionFunctor and use rfl.
The old proof also unfolded unrestrictedIntegralReductionExistence, which no
longer occurs after the shared reduction refactor. Public signatures, imports,
all prior proofs, data constructions, and DAG attachments/dependencies are retained.

Change record: coord/changes/C4-primitive-tensor-bridge-shared-reduction.md.
This is the assigned build/definition repair.

Validation: lcompile.py compiled the restored module successfully in 44.6 seconds
(exit code 0). Local scans found no live direct importers and no references to
finiteTensorBridge outside the item. tools/downstream.py cannot resolve the
currently quarantined module; the source scan includes quarantine/ explicitly.

## Proved and sorry left

Holes closed: 0 of the 2 existing holes. Holes added: 0. Split off: 0.
The finiteTensorBridge equality proof is repaired; its map is still the identity.

The two existing named theorem holes remain unchanged:

- WeilConjectures.completedPrimitiveCounit_roos_exists:
  lem-pur-completed-primitive-counit-roos-realization-existence.
- WeilConjectures.completedPrimitiveCounit_comparisons_exists:
  lem-pur-completed-primitive-counit-comparisons-existence.

## No longer needed

No imports, nodes, modules, declarations or dependencies are pruned. Only the
obsolete unfolding of unrestrictedIntegralReductionExistence,
scalarReductionExistence and scalarReductionExtension is removed from the
functor-equality proof. The existing unit route and quarantined parents stay intact.

Mathlib searches through msearch.py were run with leanfinder (completed tensor
and pullback via coherent quotient systems), loogle ("counit", "tensor"),
and grep (unrestrictedIntegralReductionFunctor|scalarReductionExtension).
The hits concern ordinary adic completion or generic monoidal counits; none
replaces this specific construction. Local source inspection gives the shorter
repair directly: unrestrictedIntegralReductionFunctor is scalarReductionExtension.

## Where the brief, the DAG or earlier work was wrong

The rework entry correctly identifies the failure caused by the shared-reduction
refactor: the previous unfold list assumes the witness occurs in the goal.
The repaired proof uses the current explicit alias. No mathematical statement,
DAG route or Lean attachment needs alteration. The absent Lean file is a
quarantined source to restore, not an authorization to withdraw it.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
