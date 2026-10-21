## What changed

Restored the quarantined modules
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison`,
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension`, and
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescent` as compatibility
re-exports of their existing, proved `WeilConjectures` counterparts.
Updated the three matching DAG Lean attachments to those canonical modules
and their actual signatures using `IsKFlatTensor`. The mathematical statements
and existing DAG proof plans are unchanged. All three old public signatures
match upstream exactly after replacing `IsAcyclicTensorKFlat` by `IsKFlatTensor`.

Each compatibility module compiles through `lcompile.py --all`. All three canonical
theorems' axiom checks report only `propext`, `Classical.choice`,
and `Quot.sound`. No source-library file is modified.

Change record: `coord/changes/E5-canonical-tensor-hom-comparison-upstream-reuse.md`.

## Proved and sorry left

This is a quarantine/API repair with zero original local holes, zero holes
closed, and zero holes added. No decomposition or new theorem is introduced.
No `sorry` remains in any delivered module. Existing complete upstream proofs
provide:

- `AlgebraicGeometry.tensorHomUncurry_normalized_comparison`
  (`lem-pc-tensor-hom-uncurry-normalized-comparison`).
- `AlgebraicGeometry.exists_tensorHomUncurry_descent_extension`
  (`lem-pc-tensor-hom-uncurry-descent-extension`).
- `AlgebraicGeometry.exists_tensorHomUncurry_descent`
  (`lem-pc-tensor-hom-uncurry-descent`).

## No longer needed

The three duplicated local proof implementations are unnecessary. Their old
proof-only imports are replaced by the canonical upstream module re-exports:

- Comparison: `WeilConjectures.AlgebraicGeometry.CanonicalTensorHomEvaluationNaturality`
  and `WeilConjectures.AlgebraicGeometry.CanonicalTensorModelInputNaturality`.
- Extension: `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison`.
- Descent: `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative`
  and `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentExtension`.

Their former direct public import of
`WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential`
is supplied transitively by the canonical re-exports.
No mathematical dependency node is pruned: the canonical proofs still use the
original argument. No module is claimed as removed from the target closure;
the compatibility paths remain available with no duplicate declarations.

## Where the brief, the DAG or earlier work was wrong

The assigned module was absent from `lean/` because the upstream sync moved it
to quarantine. Its recorded failure was the removed predicate name
`IsAcyclicTensorKFlat`, not an unfinished proof. Its own original implementation
already had zero `sorry`. The shortest route is the existing proved upstream
theorem; reproving it or restoring a duplicate declaration would be unnecessary.
The two downstream quarantined modules can likewise use the existing canonical
upstream implementations. The stale DAG attachments and historical Lean
predicate spellings are corrected in this packet.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
