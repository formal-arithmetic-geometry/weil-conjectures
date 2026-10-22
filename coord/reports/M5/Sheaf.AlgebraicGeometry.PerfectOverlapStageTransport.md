## What changed

Retire `Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport` in favour of the
unchanged official `WeilConjectures` construction. Update its DAG attachment
while preserving the statement, mathematical dependencies and unit route.
The retained compatibility theorem checks equality with the old construction
by unfolding and reflexivity.

Repair the return at 208cdfa3757: replace the stale sandbox tail component with
current main, including E2's landed proof simplification 7ef9e5524fd, then apply
only the two required import edits. E2's direct cartesian projection equations,
global restricted-composition lemma, complete proof, docstring, and reduced
proof imports are preserved verbatim. The counit consumer likewise differs
only in the two import edits. Both consumers import the official transport and
explicitly preserve the Sheaf core-comparison API formerly reexported by the
retired module. No source-library or target declaration changes.

Change record: `coord/changes/M5-perfect-overlap-stage-transport-adapter.md`.

## Proved and sorry left

Zero-hole definition retirement and repair. Initial holes: 0. Holes closed: 0.
Holes added: 0. Split off: 0. Sorries left: none.
The complete proofs of `perfectOverlapCompositeCounitFactor`,
`perfectOverlapTailProjectionComponent` and the prism chain are preserved.

Server validation through `lcompile.py --all` with `LCOMPILE_NO_LOCAL=1` passes
without warnings, including the updated tail component in 26.7 seconds.
The three prism-chain sandbox files are byte-identical validation sources.
Compatibility, consumer and axiom checks are retained in the scratchpad;
the delivery tool also checks the complete packet before pushing.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport`.
Both direct consumers instead import its official `WeilConjectures` owner.
Both DAG parents still use the same node with its canonical Lean attachment.
All mathematical dependencies and the unit route remain needed and preserved,
including any quarantined parents. No other module, declaration or node is
withdrawn. E2's import pruning remains intact.

## Where the brief, the DAG or earlier work was wrong

The previous packet retained the tail proof preceding E2's landed simplification,
so landing correctly refused its overlapping edits. This repair rebuilds that
consumer from the current source rather than reverting E2's work. Its only diff
is replacement of the public transport import and explicit preservation of the
previous comparison reexport.

An earlier return concerned the tail's quarantine. N2 restored it, and E2 then
simplified its proof. The current file is present in the library; no quarantine
archive is deleted or listed in `deleted.txt`. The current rework table has no
row for this item or the tail. Both direct consumers are unclaimed in the shared
claim snapshot; E2's completed work is preserved.

## Forced adaptations

Both consumers originally public-import the withdrawn Sheaf transport. Replace
that import with `WeilConjectures.AlgebraicGeometry.PerfectOverlapStageTransport`
and add `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons`
to preserve the previous public API. No other line differs from current main.
The earlier counterfactual check with the transport replaced by an empty module
reported unknown identifiers for `perfectOverlapStageTransport` and the stage
component API. The adapted consumers compile. The delivery tool reruns applicable
counterfactual and signature checks against its fetched base.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
