## What changed

Retired Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer,
as explicitly assigned in coord/retire-items.tsv. Its complete adopted-source
twin proves the identical conclusion with all the same category and functor
hypotheses, without the redundant common-universe Brown parameter.

Adapted the sole live consumer,
Sheaf.CategoryTheory.GrothendieckDerivedBrownRetractData: use the canonical
private import, drop the extra Brown-principle argument, and remove the import
used only by that argument. Its signatures, visibility and public imports stay
unchanged. Reattached the universe-transfer node to the source theorem, recorded
the stronger statement and both citers, and synchronized the localization-data
node with the direct source application. No source-library file changes.

Change record: coord/changes/G1-brown-universe-transfer-retirement.md.

## Proved and sorry left

Actual initial item holes: 0. Closed: 0 of 0. Added: 0. Split off: 0.
No sorry remains in a delivered Lean file. The source theorem
CategoryTheory.brownCohomologicalRepresentabilityUniverseTransfer is already
fully proved. CategoryTheory.grothendieckDerived_localization_brown_data retains
its complete proof and unchanged conclusion. This delivery is duplicate
retirement, not new proof progress.

Validation: lcompile.py compiled the adapted consumer cleanly (1.2 s), and a
scratch compatibility probe proved the complete old conditional signature from
the canonical theorem (1.0 s). Both the probe and canonical theorem report only
propext, Classical.choice and Quot.sound. The downstream scan found five
transitive importers and exactly one direct consumer/call site. Quarantine and
unit scans found no further references requiring adaptation.

## No longer needed

Withdrawn module:
Sheaf.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer.
Its sole live consumer replaces that private import with
WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer.
The consumer also removes its private import of
WeilConjectures.CategoryTheory.BrownCohomologicalRepresentability, used only to
supply the discarded extra argument. The localization-data node no longer has a
direct proof dependency on lem-pc-brown-cohomological-representability.

No DAG node is deleted. The universe-transfer and auxiliary nodes remain needed
and attached to the canonical source implementations. Brown cohomological
representability and its source module remain used transitively by the source
universe-transfer proof, and are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed obligation, but the current item has
zero holes following V4's auxiliary retirement. Its explicit retirement row
requires withdrawing the remaining conditional duplicate and adapting its
consumer, which this packet does. The old retirement consumer list names the
already-retired Sheaf BrownRepresentabilityRightAdjoint: its canonical module
already has an independent complete proof. The right-adjoint DAG proof text
still describes the older conditional route; no source file needs adaptation.
The localization-data DAG step formerly supplied hBrown, now unnecessary.
No mathematical dispute or new node is introduced. No unit statement or step,
target statement, or definition is changed.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
