## What changed

Restored the quarantined assigned module
`Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative` as a public
re-export of
`WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDescentRepresentative`.
The adopted source already contains the proved theorem
`AlgebraicGeometry.exists_tensorHomUncurry_descent_representative`. The archived Sheaf
copy fails because its K-flat hypothesis refers to the unavailable old predicate
`IsAcyclicTensorKFlat`. The source theorem uses `IsKFlatTensor`, whose definition has
identical data and meaning. Re-exporting restores the interface without a duplicate
fully qualified declaration.

Updated the existing node's `lean.statement` to the canonical predicate name and
`proof_origin` to record this restoration. Kept the Sheaf module/file attachment,
mathematical statement, proof steps, statement dependencies and proof dependency.
The source proof still uses representative coherence to show uniqueness of the
localized output, then selects that uniquely determined output when it exists and
zero otherwise. No arbitrary unresolved witness is selected.

Change record:
`coord/changes/tensor-hom-descent-representative-canonical-reexport.md`.

Validation: the restored module compiles through `lcompile.py`; theorem visibility
and `#print axioms` probes succeed. The theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`. The import-direction check permits the canonical
source import. A downstream source scan with `--allow-missing --uses` finds no live
consumers of the absent Sheaf path. A separate scan of both library roots and the
quarantine finds its archived parent and the unchanged upstream caller, recorded in
the change record. The archived parent has its own independent stale-predicate
rework; it is not changed in this delivery.

## Proved and sorry left

This is a zero-hole interface repair. The archived assigned module has zero
`sorry`s; the restored module has zero. Holes closed: none. Holes added: none.
No statements split off. The already proved
`AlgebraicGeometry.exists_tensorHomUncurry_descent_representative` remains available
at the original Sheaf import path through its canonical source module.

## No longer needed

No mathematical node or module is pruned. The archived direct public import of
`WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential` and private
import of `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryRepresentativeCoherence`
are replaced by the single canonical representative module import. Their statements
remain used through the canonical theorem and its proof. In particular,
`lem-pc-tensor-hom-uncurry-representative-coherence` stays in `proof_deps`.
No module is withdrawn and the quarantine archive is preserved.

## Where the brief, the DAG or earlier work was wrong

The rework row correctly reports a missing `IsAcyclicTensorKFlat` field in the
archived source. The adopted library already provides the canonical theorem with
`IsKFlatTensor`; both predicates express the same acyclic-total-tensor condition.
The node's stored Lean signature was stale, rather than its mathematical statement
being false. This assignment repairs that stale interface and honestly reports
zero initial and final holes. There is no open numbered return for this item in
`coord/returns/N3.md` beyond the general upstream-sync notice. No target or unit
route is changed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
