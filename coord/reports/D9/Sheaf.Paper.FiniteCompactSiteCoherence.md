## What changed

Proved six of the eleven theorem bodies in `Sheaf.Paper.FiniteCompactSiteCoherence`.
The existing signatures and all eight constructions are unchanged. The proof imports
`FiniteSiteWordRefinement` for identity normalization and uses the existing proved
refinement site equation. Private calculations establish common-refinement cancellation,
change cocycles, adjunction uniqueness for native identity factors, and identity pasting.
Only the item module and its matching proof-node update are delivered.

## Proved and sorry left

Six original holes closed, in namespace `AlgebraicGeometry.ProEtale`:
`finiteCompactSiteComparison_isIso`, `finiteCompactSite_refinement`,
`finiteCompactSite_common_refinement`, `finiteCompactSite_change_coherence`,
`finiteCompactSite_identity`, and `finiteCompactSite_refinement_coherence`.

Five original holes remain unchanged: `finiteCompactSiteCoherence`,
`finiteCompactSite_tower_independence`, `finiteCompactSite_naturality`,
`finiteCompactSite_composition_units`, and `finiteCompactSite_associativity`.
All belong to `lem-sp-finite-compact-site-coherence`; their existing source docstrings
and proof plans remain. No holes added and none split off. This is a partial proof
delivery, not a decomposition. The item compiled without warnings in 17.5 seconds; final delivery validation follows.

## No longer needed

The six proved clauses do not need `lem-sp-site-coherence-descent`,
`lem-cbc-compactifiable-cofiltered`, or tower existence: refinements are supplied and
cancellation gives their equations. These dependencies remain in the node because the
five untouched clauses retain their original proof plan. No node or module is claimed
as globally pruned. The unused attempted proof imports `FiniteSiteTowerPaste` and
proof access to `ProperOpenCoefficientMate` was removed. Proof access to
`CompactSupportSiteCoherence` is retained for its proved private site/refinement helpers. Original public construction imports remain.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. A full composition/associativity argument was attempted, but
converting the native derived functors and the compositor wrappers repeatedly exceeded
kernel heartbeat or file runtime limits. An attempted repair of the unclaimed
`CompactSupportSiteCoherence` construction did not resolve this and was withdrawn;
that module and its change record are absent from this packet. The original five
composition-related holes are preserved rather than replaced by unverified obligations.
The retained independent proofs compile separately from that attempted calculation.

The launcher resumed this sandbox through provider interruptions and compile-queue
pauses. Earlier work is preserved. The reference clock was reset on a resumed attempt
(the sandbox has `.brief2` through `.brief5`; `.budget.start` was 1792769016.5298843).
No budget or launcher file was changed by this worker.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
