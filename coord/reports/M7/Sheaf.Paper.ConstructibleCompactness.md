## What changed

Reconciled the returned packet with the current live source. The old packet is
byte-identical to the library: its canonical compact-object import repair is already
present. The revised packet removes the unused public import
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` from
`lean/Sheaf/Paper/ConstructibleCompactness.lean`. This is an actual source change
relative to current main, rather than another submission of the duplicate packet.
All declaration signatures, definition bodies, theorem proofs, attributes and
docstrings are preserved verbatim. The canonical public import of
`WeilConjectures.CategoryTheory.CompactObject` remains in place.

`tools/downstream.py` identifies 126 transitive consumers and the sole direct
consumer `Sheaf.Paper.BrownHypothesesGeneration`. The change record lists every
consumer and its current local claim holder. The static
`tools/import_prune_check.py` check passes without findings. No consumer is adapted.
The existing importing probe exercises the three public declarations, prints their
axioms and repeats the consumer's rational compactness extraction.

Change record: `coord/changes/M7-constructible-compactness-canonical-import.md`.
The revised root compiled individually in 21.0 seconds and again with its unchanged
direct consumer in 21.7 seconds. The unchanged consumer compiled against it in
27.9 seconds. Both runs completed without errors or warnings. The public importing
probe compiled cleanly in 5.0 seconds against the changed root. It checked all
public names and the consumer compactness extraction. Both public definitions
have only `propext`, `Classical.choice` and `Quot.sound`; the theorem additionally
has `sorryAx` from its existing imported dependencies.

## Proved and sorry left

The item already has zero local holes; the revised item also has zero. Holes
closed: none (0). Holes added: none (0). Split-off statements: none (0). No proof
was replaced or altered. No `sorry` occurs in any delivered declaration.

`AlgebraicGeometry.ProEtale.constructible_compactness` retains its complete proof
from the declared dependencies, some of which still have imported holes. This
packet does not claim to close those dependencies. The definitions
`AlgebraicGeometry.ProEtale.constructibleCompactnessComparison` and
`AlgebraicGeometry.ProEtale.HasConstructibleCompactness` are unchanged real data.

## No longer needed

Removed the direct public import
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`. Its arbitrary
K-injective-resolution derived-functor API is unused by this file's statements,
definitions and proofs.

The item's public-import closure consequently loses that module,
`Sheaf.CategoryTheory.KInjectiveTotalDerived`, and
`Mathlib.CategoryTheory.Triangulated.Functor`. Other proof imports still reach
these modules, so the ordinary import closure is unchanged. No whole module is
pruned from the targets, no declaration is withdrawn, and no needed mathematical
node or proof dependency is removed.

The node `sk-thm-constructible-compactness` and its dependency list stay unchanged:
the finite-window comparison, bounded-family argument, finite Postnikov induction,
and restriction to the actual localizing closure are all still implemented by the
same proofs. There are no new nodes.

## Where the brief, the DAG or earlier work was wrong

The retained report described a quarantined item needing restoration. That account
is stale: the item is live, its canonical compact-object import is already correct,
and the retained Lean file exactly matched it. The return at head 956005c8d was
therefore correct that another identical packet would contain no new Lean change.
This packet preserves the completed repair and performs the remaining unused-import
cleanup explicitly required by the stage-3 brief. It does not count the old repair
again or manufacture a new hole to claim proof progress.

The previous session's exit-143 delivery failures are historical, not evidence that
a delivery has succeeded. Only a fresh DELIVERED confirmation will establish the
new packet's delivery. No launcher script or gate has been modified or bypassed.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
