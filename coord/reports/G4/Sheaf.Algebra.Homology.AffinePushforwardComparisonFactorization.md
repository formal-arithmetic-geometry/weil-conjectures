## What changed

Withdraw the unused compatibility module
`Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization` and record the
complete canonical upstream parent argument that makes it unnecessary.

The factorization node already names
`AlgebraicGeometry.affinePushforwardComparison_factorization` in the adopted upstream
module. Its full naturality proof is complete and stays verbatim. Keep this attachment,
its two proof steps and its coordinate dependency, and explain the wrapper cleanup in
its proof-origin note.

The only DAG parent is `lem-pc-affine-pushforward-cohomology-edge-identity`. Record its
existing complete upstream theorem,
`AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity`, as its realization.
That proof uses the same construction, adjunction cancellation and final factorization
application, and imports the canonical factorization directly. Its source differs from
the archive only in copyright, that import, and six explicit sheaf-universe annotations.
All three proof steps and all mathematical dependency edges remain. The exact upstream
signature is recorded in the node.

The separately claimed Sheaf identity module belongs to P1. Neither its source module
nor its quarantine archive is edited or withdrawn. The parent-node attachment update
records the actual existing replacement proof; it does not alter any Lean module held
by P1. All adopted source-library files remain verbatim. The factorization wrapper is
listed in deleted.txt; its mathematical theorem remains available in its canonical module.

Fresh server checks: the factorization re-export compiled before withdrawal; both
canonical theorem axiom checks list exactly propext, Classical.choice and Quot.sound.
A scratch re-export of the canonical identity theorem compiles, and a scratch copy of
the upstream higher consumer with its identity import redirected through that re-export
also compiles without warnings (4.1 seconds), with the same allowed axioms. The source
comparison, dependency audit and unit-route check support the canonical-parent update.
No scratch source is delivered.

Change record: `coord/changes/G4-affine-factorization-wrapper-pruning.md`.

## Proved and sorry left

Zero-hole cleanup: 0 holes before, 0 after, 0 closed, 0 added, 0 split off.

The existing canonical proofs of
`AlgebraicGeometry.affinePushforwardComparison_factorization`
(node `lem-pc-affine-pushforward-comparison-factorization`) and
`AlgebraicGeometry.exists_affinePushforwardCohomologyEdge_identity`
(node `lem-pc-affine-pushforward-cohomology-edge-identity`) are reused in full.
No mathematical declaration is removed and no new statement is introduced.
No delivered file contains a proof hole.

## No longer needed

Prune `Sheaf.Algebra.Homology.AffinePushforwardComparisonFactorization` and its
public re-export of the upstream factorization module. The canonical upstream
identity proof imports the canonical upstream factorization directly. The parent
node records that complete proof in this same packet.

The duplicate archived Sheaf identity proof is not needed as the node's realization;
its complete canonical counterpart supplies the same statement and argument. Its
source module and archive remain untouched for the separately claimed repair.
The archived private import of the compatibility wrapper is not part of the canonical
parent proof now recorded by the DAG.

No DAG node, upstream module, coordinate definition, mathematical dependency, or
unit step is pruned. No tool_uses approval changes.

## Where the brief, the DAG or earlier work was wrong

G5's zero-hole factorization-wrapper restoration landed immediately before this
claim, and its rework row was cleared during this session. The actual theorem was
already proved. Its five explicit sheaf universes agree with the current coordinates.
The remaining cleanup is the compatibility path together with the actual canonical
parent proof and corresponding parent-node attachment update.

Zero active importers alone would not justify withdrawing the wrapper: its identity
parent still depends on the factorization node. This packet retains that mathematical
dependency and records the full existing upstream parent proof, which directly uses
the canonical factorization. The archived parent source is preserved, rather than
emptied, deleted or silently treated as withdrawn. No module held by another group
is adapted.

A source and DAG audit found one parent of the factorization node (the updated
identity node), no parent of the identity node, no active importer of the Sheaf
factorization path, and one archived importer (the preserved identity archive).
The unit's realized lists contain neither node. No target or unit statement changes.
Both canonical arguments work in every degree, without boundedness or nonzero-ring
hypotheses. This is module pruning and provider reconciliation, not a new proof
or a count of holes closed.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
