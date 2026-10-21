## What changed

Restored lean/Sheaf/Paper/CondensedConstructibleOneStep.lean byte for byte from its
coord/rework.tsv quarantine path. The complete proof of
AlgebraicGeometry.ProEtale.condensed_constructible_one_step and all nine private helpers
are retained. This repairs a missing module with zero original holes. No source-library
module, public import, signature, definition, or theorem body is changed.

The proof follows all three existing node steps: generic local finite presentation gives
the global alternative or a nonempty open; its closed complement is nonsurjective and
constructible pullback supplies the closed module; recollement gives a distinguished
triangle, mapped from D+ to D and transported along the exact single-functor isomorphisms.
The identity direct-image comparison makes the open extension a locally closed piece.
The global alternative includes the empty scheme. No scheme factorization through a
stratum or extra reducedness hypothesis is used.

Read the six dependency statements and their Lean interfaces. The node and its Lean
attachment, proof, proof_deps, proof_origin, and proper-base-change unit route remain
accurate and unchanged. The existing DAG parent is
lem-weil-pbc-condensed-constructible-extension-tower. It is preserved, as is its archived
consumer module. The change record inventories all direct and transitive consumers:
coord/changes/D4-restore-condensed-constructible-one-step.md.

Searches: LeanFinder found sheaf finite-presentation APIs, with no exact one-step theorem;
Loogle found Pretriangulated.isomorphic_distinguished, already used by the archived
transport helper; the launcher grep search found no matches. Direct rg over both library
roots and the quarantine found the archived theorem and its extension-tower application,
with no replacement declaration. Reusing the complete archived proof is the shortest route.

Validation: the byte-identical restored module compiled cleanly through lcompile.py
in 8.1 seconds against the published library. It also compiled in 20.0 seconds with a
freshly compiled, unchanged CondensedOpenClosedRecollement dependency (42.5 seconds).
The direct archived consumer CondensedConstructibleExtensionTower compiled unmodified
in 8.8 seconds against the restored item. These dependency and consumer sources are
kept only as scratch verification inputs, outside the delivered lean tree. The required
delivery runs the axiom probe.

## Proved and sorry left

Original holes: zero. Restored holes: zero. Holes closed: zero. Holes added: zero.
No statements split off. AlgebraicGeometry.ProEtale.condensed_constructible_one_step
has its complete archived proof; all nine private helpers are proved. No sorry remains
in any delivered Lean file. This is a source-restoration repair, not a proof-hole closure
or a decomposition.

## No longer needed

None. No import, declaration, node, module, Lean attachment, or dependency is withdrawn.
All six proof dependencies of lem-weil-pbc-condensed-constructible-one-step are retained.
The quarantined extension-tower parent still needs this theorem; absence from the live
library is not treated as permission to prune it. No blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assignment is the rework restoration listed in coord/rework.tsv, rather than an
unproved theorem: the preserved source has zero sorries. Initial compiler attempts
reported a dependent generalize failure and a cached Mod.monoidalClosed kernel argument
mismatch; a later compile of the byte-identical archived source succeeded. No diagnostic
proof edits or extra import-all directives are retained. The existing mathematical
statement and DAG proof plan require no correction. There are no new nodes.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
