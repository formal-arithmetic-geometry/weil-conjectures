## What changed

Completed the duplicate retirement listed in coord/retire-items.tsv for
Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent. Withdraw its file
through deleted.txt and reattach sbc-lem-higher-direct-image-limit-class-descent
to the existing source theorem
AlgebraicGeometry.Etale.exists_higherDirectImage_limit_fiber_rep in
WeilConjectures.AlgebraicGeometry.HigherDirectImageLimitClassDescent.
The Lean record contains the source signature verbatim and explains the migration.

The source theorem has exactly the same conclusion and all the same binders,
except for the unused hK transition equation. The two proof bodies are identical
except for the duplicate's binding referencing that unused hypothesis. This was
checked by a literal comparison after removing those two pieces.

No current Lean module imports the duplicate. The inventory's historical consumer,
Sheaf.AlgebraicGeometry.HigherDirectImageLimitSystem, is already absent. Its
surviving source counterpart already imports the source class descent module and
calls the source theorem without hK. It needs no edit. No adopted source file is
changed. The change record is
coord/changes/U1-retire-higher-direct-image-limit-class-descent.md.

## Proved and sorry left

This is a duplicate repair: zero direct holes initially, zero holes closed,
zero holes added, and zero holes left in the withdrawn module. The declaration
AlgebraicGeometry.Etale.exists_higherDirectImage_limit_fiber_rep was already
proved in both modules. No theorem is split off. Existing transitive proof
obligations remain attached to their existing nodes and are not counted as closed.

The source replacement and the unchanged actual parent
AlgebraicGeometry.Etale.isIso_higherDirectImage_limit_system were copied into the
sandbox scratch directory for single-file server compilation with lcompile.py.
The scratch copies are validation artifacts and are not delivered. The initial
two-file request and subsequent individual requests returned code 124 with
"no answer from the compile server"; neither file was compiled in this session.
Both files are unchanged published sources. There are no new or adapted Lean
proof modules in this packet; the delivery tool runs its withdrawal preflight.

The same proof handles degree zero, singleton directed systems, and empty etale
neighborhoods. Removing an unused hypothesis does not alter any of these cases.
No definition or target statement changes.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.HigherDirectImageLimitClassDescent.
Its public imports and its private presheaf-class-descent import disappear with
the duplicate; the identical imports remain in the source replacement. No further
mathematical dependency is pruned. In particular,
lem-sbc-higher-direct-image-limit-presheaf-class-cover is still required and
remains in proof_deps; its source theorem is the first step of the source proof.

The only semantic parent citing this item in stmt_deps, proof_deps, or proof-step
uses is sbc-lem-higher-direct-image-limit. That parent's existing Lean attachment
is WeilConjectures.AlgebraicGeometry.HigherDirectImageLimitSystem, which already
uses the source replacement. Preserve the parent dependency edge and the item's
mathematical statement and proof. No DAG node is withdrawn. No quarantined
consumer imports the duplicate. tools/downstream.py reports zero current
modules downstream of it. The unit sk-lem-failure-field and its realization
record are unchanged; no step of its route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief names a module with no remaining direct sorry. The
current retirement inventory supplies the actual repair. Its DIFFERENT label
records the source's omission of the unused hK binder, which is a harmless
strengthening: fiber class descent uses hη and naturality of η, not the equation
for K.map. The inventory's sole consumer has already migrated to its source twin.

LeanFinder and Loogle searches via msearch.py found general scheme-limit and
point-fiber lemmas; the grep search found point-fiber representation APIs. The
library search found the exact stronger source theorem, whose proof follows the
existing DAG steps. No new geometric lemma, new node, or further decomposition
is needed. The source-library boundary is preserved in full.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
