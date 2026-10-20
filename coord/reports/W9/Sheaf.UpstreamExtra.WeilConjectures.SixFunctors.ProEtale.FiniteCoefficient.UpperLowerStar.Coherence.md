## What changed

Reapplied the scope repair to the current quarantined source recorded in
`coord/rework.tsv`. The live item path is currently absent; the current source is
`quarantine/Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Coherence.lean`.
Compared it with the retained delivery, then regenerated the sandbox module from
that source rather than resubmitting the returned packet unchanged.

Removed the empty `Site` and `Eta` sections, including the two dangling
`omit ... in` commands responsible for the recorded `Unexpected name Eta after end`
error. Collapsed the five repeated `omit ... in` commands before the associativity
lemma to one and wrapped the generated header comment.

Preserved both public theorem signatures. Their proofs now apply the matching
current upstream results `ProEtale.lowerStarComp_assoc` and
`ProEtale.lowerStarComp_id_left` directly, instead of repeating the legacy
isomorphism calculations. The final module compiled cleanly through `lcompile.py`
in 1.4 seconds. No upstream source file, definition, instance, or target changed.

Change record: `coord/changes/W9-finite-coefficient-coherence-scopes.md`.

## Proved and sorry left

Zero-hole rework repair: 0 holes before, 0 after; 0 closed, 0 added, 0 split off.
The two retained proved declarations are
`AlgebraicGeometry.ProEtale.coefficient_lowerStarComp_assoc` and
`AlgebraicGeometry.ProEtale.coefficient_lowerStarComp_id_left`.
No declaration containing `sorry` remains in the delivery. No DAG node attaches
to this module in the current repository, and no new node is needed.

## No longer needed

Removed the redundant direct public import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`:
the retained upstream `Coherence` module already publicly re-exports it.
The new proof bodies use the current upstream coherence theorems directly.
No dependency module or node is pruned: upstream still uses its legacy import.
Exact import and declaration searches found no consumers of this item or its two
coefficient-prefixed declarations in `lean/` or the other quarantined modules.

## Where the brief, the DAG or earlier work was wrong

The current return for head `2551dae6b3` reports a concurrent write after
base `e0d550965`. Re-read the current return, claim and rework records and compared
the retained packet with the current quarantine source. The live source remains
absent and the archive still contains both original theorem bodies and the
broken scopes. Regenerated the sandbox module from that archive and applied the
scope repair and upstream-proof simplification there. The archive is retained;
no withdrawal is requested. The delivery tool constructs the new commit against
the freshly fetched branch.

This is a quarantined compile repair with zero holes, not an unproved DAG item.
The scheduled sync retained `omit ... in` modifiers after removing their
declarations. Those modifiers opened unnamed scopes around `end Eta`, breaking
scope closure. No mathematical statement was disputed or weakened.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
