## What changed

Replaced the sole hole in
`lean/Sheaf/TraceFormula/CompactSupportDirectImageOrdinaryEvaluation.lean`
with a direct ringed-site construction. The original declaration, universes,
hypotheses, conclusion and public import are preserved.

For each level, the two coefficient-ring identifications have identity components.
The system direct-image coefficient map at `(n,U)` is the finite direct-image
coefficient map at `U`. This proves the square of coefficient maps commutes.
Mathlib's `SheafOfModules.pushforwardComp` and `pushforwardCongr` then construct
the isomorphism. Their components are identity functions on the underlying
sections, giving the required heterogeneous equality.

Updated the item's DAG proof to describe this construction. No new modules,
public declarations, definitions or assumptions are introduced. A scoped
heartbeat allowance lets Lean elaborate the nested scalar restrictions; it
changes no definition or instance, and the 60-second per-file runtime limit
is unchanged. Profiling options have been removed.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.compactSupportDirectImageOrdinaryEvaluation`
(node `lem-trf-compact-support-direct-image-ordinary-evaluation`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
This is a proof rather than a decomposition; nothing is split off.

## No longer needed

None. The sole original public import
`Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram` is needed by the
statement and is retained. The node dependency
`def-trf-compact-support-system-evaluation-diagram` is retained. No quarantined
parent, dependency, Lean attachment or unit route is withdrawn.

The proof uses no derived evaluation comparison, K-injective-resolution
comparison or additional semilinear-system splitting lemma. The existing
Mathlib pushforward composition and congruence API suffices for the ordinary
square. No formerly declared dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The previously split ordinary obligation has a direct proof from the concrete
pushforward definitions; no further split is needed.

At session start the item and its direct dependency were quarantined, so the
source was read at the path recorded by `coord/rework.tsv`. Both have since
been restored in the shared checkout. This delivery preserves the direct
`CompactSupportSystemEvaluationDiagram` dependency, its declarations, and the
item's original Lean attachment. It does not withdraw any archive.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
