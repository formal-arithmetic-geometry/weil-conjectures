## What changed

Restored `lean/Sheaf/Paper/CondensedConstructibleOpenClosedImages.lean` from the
quarantine source named by its current rework row. Repaired the proof of
`AlgebraicGeometry.ProEtale.CondensedRing.constructible_open_closed_images`:
obtain the abelian closed counit from `ProEtale.abelian_closed_support`, transport
it with the existing proved `moduleCounitOfAbelian` helper, and use its actual
counit isomorphism. The existing constructibility, vanishing and scalar transport
argument then compiles. Added only the private proof import of
`Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`. Preserved the archived
signature, universes, public imports, node attachment and all previous dependencies.
Updated the node's proof, proof dependencies and proof origin for this argument.

The repaired module compiles cleanly with lcompile.py (3.6 seconds). The archived
signature was compared verbatim with the restored declaration. The change record
is `coord/changes/D3-restore-condensed-constructible-open-closed-images.md`.

## Proved and sorry left

This is a restoration and proof repair, with zero holes in its authoritative
quarantined source. The restored theorem
`AlgebraicGeometry.ProEtale.CondensedRing.constructible_open_closed_images`
(node `lem-weil-pbc-condensed-constructible-open-closed-images`) is fully proved.
Holes closed: 0. Holes added: 0. Sorry left: none. No split-off statements.
The theorem retains arbitrary commutative condensed coefficients and permits
empty pieces and zero modules; no geometric or coefficient hypothesis was added.

## No longer needed

No imports, nodes or modules are pruned. The full
`condensed_open_closed_recollement` theorem is no longer invoked merely to
extract its abelian-level counit. Its module and dependency node remain needed
for the proved private counit-transport and open-restriction vanishing helpers.
All archived dependency imports remain used.

## Where the brief, the DAG or earlier work was wrong

The live item source was absent because of the recorded cluster-restore revert,
not because its mathematics was withdrawn. Its quarantine source had no sorry.
Compiling that source reproduced a `Tactic generalize failed: result is not type
correct` error at the obtain-pattern eliminating the large dependent existential
of `condensed_open_closed_recollement`. The repaired argument bypasses that
elimination using the already proved abelian closed-support input and coefficient
transport helper. It preserves the statement and the blueprint unit route.

All three direct consumers found by scanning live and quarantined Lean sources
are quarantined: `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing`,
`Sheaf.Paper.IntegralTensorShriek`, and `Sheaf.Paper.ProperHeartBoundTorsion`.
Their imports and theorem uses need no adaptation: the archived signature and
public imports are identical. `tools/downstream.py` reports the live item as
unknown because the live source is absent, so this consumer inventory also scans
the quarantine tree. No consumer or other group's module is modified.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
