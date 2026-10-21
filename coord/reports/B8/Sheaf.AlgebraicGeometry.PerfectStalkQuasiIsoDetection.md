## What changed

Retire the zero-hole duplicate
`Sheaf.AlgebraicGeometry.PerfectStalkQuasiIsoDetection` in favour of the already
proved adopted source module
`WeilConjectures.AlgebraicGeometry.PerfectStalkQuasiIsoDetection`. The duplicate
is listed in `deleted.txt`; no file under `lean/WeilConjectures/` and no target
statement is changed. The node
`lem-sc-perfect-stalk-quasi-iso-detection` is reattached to the adopted source
declaration, with its source signature, proof route and dependencies recorded.

The source theorem is stronger because it omits the unused `IsAffineOpen U`
hypothesis `hU`; the old node statement follows by specialization. The source
implementation is the complete finite-free stalk, K-projective, chain-map lift,
and inverse-homotopy spreading argument. A scratch specialization compiled
successfully with `lcompile.py` (3.6 seconds).

## Proved and sorry left

This is a retirement repair, not a new proof. The item had zero textual sorries;
zero were closed, zero were added, and zero were split off. The retained upstream
theorem is already proved. No delivered declaration contains `sorry`.

## No longer needed

Withdrawn module: `lean/Sheaf/AlgebraicGeometry/PerfectStalkQuasiIsoDetection.lean`.
Its duplicate private K-projective helper and its six direct proof imports leave
the live Sheaf tree with the file. The current source tree has zero direct or
transitive importers of the Sheaf duplicate; the adopted source parent already
imports the upstream theorem directly. No mathematical dependency node, parent
edge, unit statement, or unit proof step is pruned. The dependency nodes for
perfect complexes, open stalks, free projective stalks, chain-map lifting,
canonical restriction comparison, and inverse-homotopy spreading remain in the
DAG through the adopted proof route.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes a theorem with a proof hole, but the current
queue explicitly marks this item as a `retire` repair and the duplicate module
already has a complete proof. Keeping both declarations would preserve a
redundant implementation after the adopted source theorem landed. The old DAG
attachment pointed to the duplicate Sheaf file; it now points to the unchanged,
proved adopted source declaration. The source theorem omits `hU`, which is unused
in the duplicate proof, so this is a strict strengthening rather than a weakened
statement. Mathlib searches via `msearch.py` (grep, Loogle, and LeanFinder)
found no independent perfect-stalk quasi-isomorphism theorem; direct source
search identified the adopted implementation.

## New nodes

None.

The change record is `coord/changes/B8-retire-perfect-stalk-quasi-iso-detection.md`.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
