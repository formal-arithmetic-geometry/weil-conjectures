## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Etale.ordinaryFiniteRootGenerator_naturality` by a proof composing
the naturality of the extension/restriction-of-scalars adjunction unit with the
naturality of the sheafification unit, after forgetting to additive groups.
All declaration signatures, definitions, and imports are unchanged.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.ordinaryFiniteRootGenerator_naturality`
(blueprint: `def-asd-ordinary-finite-p1-kummer-class`).
Original holes: 1. Holes closed: 1. Holes added: 0. Holes remaining: 0.
No intermediate statements were split off.

## No longer needed

None. No new proof dependencies or proof imports are needed. The proof implements
the naturality argument already given in the declaration's docstring. The public
imports support the existing coefficient, derived-category, Picard, and Kummer API.
No DAG node or module becomes unnecessary through this local proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. This is a definition node with an empty DAG
proof; its attached naturality theorem has the complete intended argument in its
existing docstring. The proof applies for every stated N and A, without an
invertibility or nonzero hypothesis: it uses functoriality alone, so also covers
N = 0 and the zero ring.

Search: LeanFinder returned module-sheaf scalar-action lemmas but no more direct
match. Loogle found no result for `NatTrans.naturality`; textual searches found
the existing naturality API and `ModuleCat.forget₂_map_restrictScalars`. The proof
uses the naturality field directly, reassociates the resulting maps, and applies
`ModuleCat.forget₂_map_restrictScalars`.

Validation: the complete module compiled through `lcompile.py` with exit code 0
and no warnings (57.7 seconds).

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
