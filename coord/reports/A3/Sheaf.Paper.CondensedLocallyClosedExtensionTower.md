## What changed

Restored lean/Sheaf/Paper/CondensedLocallyClosedExtensionTower.lean verbatim from the
quarantine path in its coord/rework.tsv row. Its live path was absent after a cluster
restore. This reinstates the complete proof of
AlgebraicGeometry.ProEtale.exists_condensedLocallyClosed_extension_tower and the proved
private helpers pushforward_piece and pushforward_tower. The existing signature, public
and private imports, declaration docstring and mathematical route are preserved.

The proof composes closed immersions to push pieces forward, maps distinguished triangles
to push finite towers forward, and uses noetherian induction on closed supports. A proper
closed immersion gives a strictly smaller support because the ambient closed immersion is
injective. The one-step distinguished triangle then adds one extension. Empty schemes and
the zero-iterate case are retained. There is no new existential choice of data or definition.

The existing node lem-weil-pbc-condensed-locally-closed-extension-tower retains its Lean
attachment, statement, proof steps and dependencies. Only its proof_origin note records
the restoration. The sk-thm-properbasechange unit route is unchanged.
Change record: coord/changes/A3-restore-condensed-locally-closed-extension-tower.md.

The item compiled alone in 3.5 seconds. A consumer check compiled the item in 5.1 seconds
and both unchanged archived direct consumers: IntegralConstructibleSheafHom in 8.0 seconds
and IntegralTensorShriek in 19.7 seconds, without errors or warnings. Consumer copies were
moved to scratchpad/ and are not part of this delivery.

## Proved and sorry left

This is a zero-hole restoration. The archived theorem
AlgebraicGeometry.ProEtale.exists_condensedLocallyClosed_extension_tower already has a
complete proof, which compiles against the current dependencies. Holes closed: 0 of 0.
Holes added: 0. Holes left: 0. No statements were split off. Both private helpers are proved.
The restored source supplies an absent theorem rather than claiming a new proof closure.

## No longer needed

None. The public import CondensedLocallyClosedPiece supplies the predicate used in the
statement. The private import CondensedLocallyClosedOneStep supplies the decomposition
and exact closed pushforward witness. Both declared proof dependencies remain needed;
no node or module is pruned.

LeanFinder found no replacement constructible-sheaf extension-tower theorem. Loogle found
ObjectProperty.extensionProductIter and its successor and zero lemmas; the proof already
uses that API. Local searches of the source library and Sheaf found no replacement for
this coefficient-generic theorem. The existing finite induction is the required route.

## Where the brief, the DAG or earlier work was wrong

The module is absent because it was quarantined, not because its statement was withdrawn.
Its rework row authorizes restoring the preserved module. The archive contains zero sorry
proofs, so this delivery restores availability and does not count as closing a proof hole.
No Lean repair was necessary: the archived argument compiles unchanged against the current
one-step theorem. Both archived consumers also compile unchanged against the restoration.
The downstream.py query reports an unknown module because the live path is absent; direct
live/archive import and declaration-use searches and DAG-parent searches supply the
consumer inventory instead. No tool was modified or bypassed for delivery.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
