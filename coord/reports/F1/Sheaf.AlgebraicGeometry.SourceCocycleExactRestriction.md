## What changed

Completed the zero-hole retirement listed in coord/retire-items.tsv. Withdraw
lean/Sheaf/AlgebraicGeometry/SourceCocycleExactRestriction.lean via deleted.txt.
It is a completely proved obsolete duplicate, not an outstanding proof obligation.

Keep both existing needed implementations: the canonical source theorem
AlgebraicGeometry.Etale.sourceCocycleExactRestriction and the original-model theorem
AlgebraicGeometry.Etale.smallModel_sourceCocycleExactRestriction. The latter already
realizes lem-weil-pbc-source-cocycle-exact-restriction in StrictLocalSmallModel.
The old duplicate mixed the unprefixed source helper names with the original small
coordinate-ring-colimit scheme; its fully qualified name also collided with the
canonical theorem. Removing it leaves the two models explicitly named.

The item's node retains its existing attachment, full statement and dependencies.
Its proof now spells out the actual smallModel_ helper names. The sole DAG parent's
proof text now identifies its existing StrictLocalSmallModel implementation and
application of the retained small-model theorem. Its attachment and dependency edges
are unchanged. No Lean consumer requires adaptation: the original-model parent already
uses the retained theorem, and the historical listed consumer already re-exports the
canonical source implementation.

Change record: coord/changes/F1-retire-source-cocycle-exact-restriction.md.

Validation: compiled the original item (18.5 seconds) and an unchanged source copy of
the retained small-model exact restriction module (20.5 seconds). A scratch compatibility
theorem repeats the old public signature, including arbitrary tau, every integer degree,
all let bindings and the original evaluation/homology-section formulas, and proves it
by exact smallModel_sourceCocycleExactRestriction. To avoid loading colliding cached
legacy modules together, the three model-independent evaluation constructions are
copied verbatim into a private scratch namespace; no mathematical hypothesis or
conclusion is changed. That proof compiles and has only propext, Classical.choice and
Quot.sound. Separate canonical and small-model consumer probes check their actual
parent comparison theorems and the two retained cocycle theorems under the same axiom
criterion. Scratch checks are not delivered library modules.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. No sorry remains in the delivered
packet; no new theorem or definition is introduced into the library.

The already proved original-model declaration is retained as
AlgebraicGeometry.Etale.smallModel_sourceCocycleExactRestriction, with node
lem-weil-pbc-source-cocycle-exact-restriction. Its existing parent theorem is
AlgebraicGeometry.Etale.smallModel_sourceLocalizedSectionsIso_germ. The canonical
AlgebraicGeometry.Etale.sourceCocycleExactRestriction and its parent
AlgebraicGeometry.Etale.sourceLocalizedSectionsIso_germ remain fully proved and unchanged.
The discarded copy's three private proof helpers introduce no lost obligation: both
retained modules contain complete versions of that projection/restriction/transport
calculation. This is retirement, not a new proof or decomposition.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction.
Its public imports WeilConjectures.AlgebraicGeometry.SourceLocalizedCocycleHomology and
Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact disappear only from the
withdrawn module; both dependency modules remain needed and are retained. No mathematical
node or dependency edge is pruned, including the exact-sections node.

The library-wide import scan reports no live importer of the obsolete module.
The quarantine scan also finds none. A structural scan of DAG stmt_deps, proof_deps
and proof-step uses finds the one parent above, which already uses the retained
original-model replacement. Its dependency is preserved and the same delivery updates
its proof text to name that actual replacement. The unit sk-prop-h2 has no realized
statement or step using this obsolete provider. The human-approved retirement request
is therefore reconciled with both the current parents and the current source, rather
than inferred merely from zero live importers. Historical C2 rework rows remain
historical records; no archive is deleted or replaced.

## Where the brief, the DAG or earlier work was wrong

The generic dispatcher brief describes a repeated unsolved proof split. This current
assignment instead has zero holes and an explicit retirement row. Both mathematical
implementations and their parent proofs are already complete.

The retirement inventory's historical consumer is no longer an importer, and its
historical node attachment has already moved to StrictLocalSmallModel. Its DIFFERENT
classification is material: the canonical source theorem uses strictLocalization,
whereas the original-model statement uses strictHenselizationScheme. Accordingly the
needed original-model node is not rebound to the canonical theorem. The full original
claim remains available from the existing smallModel_ theorem, as the compatibility
check verifies. The parent's old proof prose said adopted/re-exported implementation
even though its current Lean attachment and proof use StrictLocalSmallModel; this prose
is corrected without changing its mathematics.

An initial combined probe encountered a duplicate injectiveSections theorem through
legacy cached public imports. The current common source declarations and the two
models are therefore checked in their separate consumer environments, and the exact
old-statement comparison uses private copies of the original evaluation formulas.
No unrelated module or tool was changed to bypass that collision.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
