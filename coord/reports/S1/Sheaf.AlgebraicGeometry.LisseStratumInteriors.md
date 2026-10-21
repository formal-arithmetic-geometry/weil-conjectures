## What changed

Completed the listed retirement of `Sheaf.AlgebraicGeometry.LisseStratumInteriors`
in favour of `WeilConjectures.AlgebraicGeometry.LisseStratumInteriors`. The old module
already compiled with zero holes. This delivery withdraws the duplicate through
`deleted.txt` and redirects node `lem-weil-pbc-lisse-stratum-interiors` to the existing
upstream theorem `AlgebraicGeometry.Scheme.lisse_on_stratum_interiors`.

The public signatures are definitionally equal: `IsLisseEtaleSheafOfSets` abbreviates
`IsFiniteLocallyConstantSheafOfTypes`. The node describes the upstream proof's proved
algebraically-closed/separably-closed stalk comparison. All other dependencies and
parent edges remain. No source-library file, target, definition or consumer changes.

Validation: the existing module, unchanged upstream proof, unchanged upstream
`GenericFiniteSourceLisse` consumer, and a scratch direct application of the upstream
theorem to the exact old signature compile through lcompile.py. The application
and upstream theorem use only propext, Classical.choice and Quot.sound. Searches
in both Lean roots and quarantine find no remaining importer of the duplicate.
Change record: `coord/changes/retire-lisse-stratum-interiors-S1.md`.

## Proved and sorry left

Original item holes: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No sorry remains or is added. The existing proved
`AlgebraicGeometry.Scheme.lisse_on_stratum_interiors` is supplied by the upstream
twin. The two proved private helpers `finiteLisse_of_iso` and
`finiteLisse_of_range_subset` disappear with the duplicate; their upstream versions
remain. This is a completed retirement, not a proof-hole reduction or decomposition.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.LisseStratumInteriors`, including its duplicate
private helpers and its imports of EtaleSheaves, GenericConstancy,
FiniteLocalAbelianForget, EtaleInverseImageAlgebraicStructures and
PullbackFiniteLocallyConstant. Those APIs remain used through the upstream provider.
No mathematical node is pruned: the parent
`lem-weil-pbc-finite-source-generic-lisse` still needs the result and already imports
its upstream implementation. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not identify the actual zero-hole retirement task;
`coord/retire-items.tsv` supplies it explicitly. Its historical consumer has already
retired, and both prerequisite twins have already migrated. The DIFFERENT label
reflects the canonical predicate spelling and the upstream proof's stalk comparison,
not a changed mathematical statement. The node's old recorded signature was stale;
its Lean record now quotes the actual upstream signature.

Read both complete proofs, the parent dependency, the unit record and the cited
blueprint proof. Launcher LeanFinder, Loogle and grep found no exact Mathlib result;
repository search found the existing upstream theorem. Empty strata and empty
interior union are allowed without introducing any additional hypothesis.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
