## What changed

Restored Sheaf.AlgebraicGeometry.BottomChainModelPullbackTransport from its
quarantine archive, as required by the current rework assignment. Replaced its
public import of Sheaf.AlgebraicGeometry.DerivedPullback with
WeilConjectures.AlgebraicGeometry.DerivedPullback, the adopted canonical definition.
Added a commented, theorem-local maxHeartbeats 800000 allowance; the default
200000 exhausted during elaboration, while the complete proof compiled in 21.6 s.
The 60-second file limit is unchanged. The theorem's signature, docstring and proof
body are identical to the archive. All existing DAG attachments and dependencies
remain valid. Change record:
coord/changes/U4-bottom-chain-pullback-upstream-restoration.md.

The proof still constructs termwise localized pullbacks, uses the single natural
perfect counit and open-restriction comparison, reflects the resulting square
through the derived equivalence, and applies zeroth homology. This preserves the
specified morphism and handles zero terms, rank zero and empty opens without
additional hypotheses. The unit route is unchanged.

The downstream source check finds no live consumers. A separate quarantine/DAG
search finds PerfectUniversalH0TruncationPullback, whose application at lines
126-127 has exactly the restored argument order. That parent remains quarantined
with its own old derived-pullback import and is not changed in this repair.

## Proved and sorry left

This is a zero-hole rework item. The archived and restored modules each have zero
sorry declarations. Holes closed: none (0). Holes added: none (0). Holes remaining:
none (0). No split-off statements.

The existing complete proof of
AlgebraicGeometry.Scheme.bottom_chain_model_pullback_transport is retained and
compiled against the canonical upstream definition. Its node is
lem-sc-bottom-chain-model-pullback-transport. Its fully proved private helper
compose_squares is unchanged. The delivery probe checks their axioms independently.

## No longer needed

Removed the stale public import Sheaf.AlgebraicGeometry.DerivedPullback and
replaced it with the canonical upstream module. This is an import repair, not
withdrawal of its node or of the canonical derived-pullback dependency.
No modules or DAG dependencies are pruned. In particular the localized perfect
model, natural perfect counit, perfect-complex definition and universe-aware
open-restriction comparison remain necessary. No upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The item was absent from lean/ because of quarantine, not because it was unused.
The archive already contained a complete proof with zero holes. Its recorded
upstream-sync failure is repaired by selecting the adopted source-library
implementation. The newer environment also exhausts the default elaboration
heartbeat count; a local allowance fixes this within the existing wall-clock limit.
The DAG's statement and proof plan require no correction. Searches with leanfinder,
loogle and project grep yielded generic localization/homology tools, not a shorter
replacement for the existing natural square argument. No new nodes are needed.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
