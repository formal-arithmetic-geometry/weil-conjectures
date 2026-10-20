## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PerfectUniversalH0TruncationPullback.lean`
from its quarantined source and reinstated the complete proof of
`AlgebraicGeometry.Scheme.perfect_universalH0_truncation_pullback_isIso`.
The theorem signature, hypotheses, conclusion, namespace and proof route are unchanged.
The proof uses the existing local chain model and pullback transport lemmas, the proved
bottom homology calculation, and open-cover detection. Because the old
`Sheaf.AlgebraicGeometry.DerivedPullback` shim is now an empty withdrawn module, the
restored module also publicly imports `WeilConjectures.AlgebraicGeometry.DerivedPullback`
to expose the `derivedPullback` API used in its unchanged public statement. The interface
change is recorded in `coord/changes/Q2-perfect-universal-h0-truncation-pullback-derived-import.md`.

## Proved and sorry left

The item's one declaration is proved:
`AlgebraicGeometry.Scheme.perfect_universalH0_truncation_pullback_isIso`.
No `sorry` remains in this module, and no new `sorry` or named split theorem is added.

## No longer needed

No imports, DAG nodes, or modules were removed. The proof uses both structural
dependencies recorded by the node (`lem-sc-perfect-universal-h0-local-chain-model` and
`lem-sc-bottom-chain-model-pullback-transport`) and
`WeilConjectures.Topology.SheafIsomorphismLocalOpenCover`; no dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The archived proof itself was complete. The only current-tree incompatibility was
infrastructure drift: the former `Sheaf.AlgebraicGeometry.DerivedPullback` compatibility
module has been withdrawn, while this theorem's unchanged statement mentions
`derivedPullback`. The direct upstream public import is therefore required for the
restored module to elaborate. No statement or definition is disputed, and no target
statement is changed.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
