## What changed

Retire `Sheaf.AlgebraicGeometry.SupportedOpenPushforwardLocalComparisons` in favour of
`WeilConjectures.AlgebraicGeometry.SupportedOpenPushforwardLocalComparisons`, as listed in
`coord/retire-items.tsv` and authorized by the human-approved retirement hand-off.
The official module already proves the same three named declarations, with unused hypotheses
removed. The first omits `hTU`; the second and combined theorem omit `hTU` and perfectness.
Each original DAG statement follows by specialization of the recorded upstream declaration.
The three DAG Lean records now point at those official declarations and record their exact
signatures and this specialization. Node statements, proof steps, dependencies and unit stay.

The former consumer `Sheaf.AlgebraicGeometry.SupportedOpenPushforward` has already migrated:
its source module is absent and its DAG record points at the official `SupportedOpenPushforward`.
That official consumer imports the official comparisons and uses its stronger API (no `hTU`
argument and no perfectness argument to the local comparison). No current Lean source imports
the retired copy. There are no consumer edits and no upstream edits in this packet.

Change record: `coord/changes/retire-supported-open-pushforward-local-comparisons-K9.md`.

## Proved and sorry left

Zero initial holes, zero holes closed, zero holes added, zero remaining holes in the item.
No decomposition or split-off. All three existing proofs are adopted from the official module:
`AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons_first`,
`AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons_second`, and
`AlgebraicGeometry.Scheme.supported_open_pushforward_local_comparisons`.
This is a duplicate retirement, not new proof credit.

Validation: the unchanged official `SupportedOpenPushforward` consumer compiled through
`lcompile.py` in 9.1 seconds. The three comparison declarations and that consumer's main theorem
all report exactly `propext`, `Classical.choice`, and `Quot.sound` under `#print axioms`.
`tools/downstream.py` reports zero current modules downstream of the withdrawn copy.
A separate scratch compatibility check compiled all three original signatures directly from
the official theorems (49.2 seconds; only expected unused-`hTU` warnings in the scratch examples).
No scratch files are part of the delivery.

## No longer needed

The entire duplicate module `Sheaf.AlgebraicGeometry.SupportedOpenPushforwardLocalComparisons`
is retired through `deleted.txt`. Its two public imports and twelve proof imports disappear
with the copy; the official twin retains the identical imports required by the actual proofs.
No mathematical dependency node is pruned: the three nodes and all parent dependencies are
preserved, with their Lean attachments redirected. No remaining consumer import needs rewriting.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item containing `sorry`; this is actually the listed
zero-hole retirement item. The retirement inventory's former consumer has since retired too.
The upstream comparisons are stronger than the old recorded Lean signatures, so simply changing
the module field without updating the signatures would leave inaccurate attachments. The new
records state the exact official types and explain how they imply the unchanged DAG statements.
No mathematical error or change to the unit route was found.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
