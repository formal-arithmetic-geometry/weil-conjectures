## What changed

Restored `lean/Sheaf/Paper/TensorHomExchange.lean` from the exact quarantine path
listed in `coord/rework.tsv`. Added a local irreducibility restriction before the
rational interface for `rationalDerivedPullback`,
`sfRationalConstructibleLocalization`, `sfRationalScalarExtension` and
`rationalDerivedInternalHom`. This prevents endpoint unification from expanding
chosen derived/scalar-localization constructions. All archived declarations,
mathematical definitions, signatures, docstrings, imports and proofs are preserved.

Change record: `coord/changes/E4-tensor-hom-exchange-rational-transparency.md`.
This is the assigned quarantined-module elaboration repair, not a proof delivery.

## Proved and sorry left

Holes closed: 0. Holes added relative to the quarantined source: 0. Split off: 0.
The restored module has exactly one existing hole:
`WeilConjectures.ConstructibleTensorHom.exists_family`, whose source, complete
natural-language proof and Lean attachment are in `sk-thm-sf-tensor-hom`.
The archive compiled unchanged in 45.1 seconds against the current published build.
The repaired module compiled without diagnostics in 35.3 seconds, within the
unchanged 60-second limit. Delivery preflight checks the final packet.

## No longer needed

None. No import, declaration, module or DAG dependency is removed. The existing
unit route and the quarantined item's Lean attachment are preserved. No claim of
mathematical pruning is made from the absence of current Lean importers.

## Where the brief, the DAG or earlier work was wrong

The item is absent from `lean/` because it is quarantined, not withdrawn. The
rework row records `isDefEq` heartbeat exhaustion at rational normalization and
the ordinary rational direct-image coefficient mate; the missing identifiers
following those errors were cascading failures. On the current published build,
the original archive already compiles. The delivery restores it with a local
transparency restriction at that interface to avoid unfolding those chosen
functors during endpoint comparison.

The current blueprint also includes duality consequences (2) and (3); this repair
preserves the existing exchange statement and does not claim to formalize those
additional assertions or prove the existing `exists_family` theorem.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
