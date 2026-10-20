## What changed

Repaired `closedSupport_lowerStarExact` to state the quasi-compact-open-complement case
of its blueprint, and proved it from `closedSupportAdjunction`: closed direct image is a
left adjoint and therefore preserves finite colimits. The derived adjunction, triangle
and fibre proof install exactness from their existing complementary-open hypotheses.
The change record is `coord/changes/C2-condensed-closed-support-exactness.md`.

## Proved and sorry left

Replaced the sole hole, `closedSupport_lowerStarExact`
(node `det-lem-formal-closed-support-adjunction`), by a complete proof of the repaired
source statement. This is a statement repair, not a proof of the old unrestricted claim.
The item has zero holes. No holes or split nodes are added.

## No longer needed

No import removed from the item; no new dependencies or nodes. The former twelve consumer
adaptations are unnecessary because those modules were moved to quarantine by the project
during this session. They are retained only in scratchpad/pre-quarantine-packet and are
excluded from this delivery. No quarantined module is restored. The active direct importers
`ProEtaleFiniteLocallyProjective` and `CondensedPullbackTensorComparison` do not use the
changed exactness or derived declarations and need no adaptation.

## Where the brief, the DAG or earlier work was wrong

The old global instance omitted the quasi-compact open-complement hypotheses of the node
and cited Stacks result. The repair restores those hypotheses; no target statement changes.
An earlier 13-module packet passed dry run at ca57712166 but its push stopped on a consumer
compile timeout. Generic private comparison helpers subsequently made that consumer compile
in 11.9 seconds. The consumer work is retained in scratchpad, because the active library
later quarantined all twelve consumers. The resumed dry run incorrectly appeared to add
three holes only because it treated those removed consumer modules as new; removing them
from the packet resolves the baseline mismatch without changing any proof.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
