## What changed

Filled the three object-identification theorems in
`Sheaf.SixFunctors.FrobeniusPointTransportNatural` using the object specifications of
`rationalDerivedPullback_existsUnique`, `commonStageDerivedPullback_existsUnique`, and
`pointQbarFibre_existsUnique`. The common-stage equality additionally applies the rational
object equality at the object's own coefficient stage. All signatures, definitions,
docstrings, imports, and the node's proof route are unchanged.

## Proved and sorry left

Closed three of the four original holes:

- `WeilConjectures.frobeniusPointRationalPullbackEq`.
- `WeilConjectures.frobeniusPointQbarPullbackEq`.
- `WeilConjectures.frobeniusPointQbarFibreObjEq`.

One original hole remains:
`WeilConjectures.frobeniusPointTransport_natural`, node
`lem-weil-frobenius-point-transport-natural`. No holes were added or split off.
The object proofs use existing stated specifications whose proofs remain work in their
respective modules; they do not claim to close their transitive axiom dependencies.

The main naturality proof was explored through chain restriction, fully faithful derived
localization, comparison naturality, and rational denominator clearing. That unfinished
experiment is not part of the delivery. The standing brief explicitly permits a delivery
that closes some holes in a module and leaves the others untouched.

## No longer needed

None. No imports, modules, or DAG dependencies are removed. The remaining naturality
statement retains its existing four-step plan and its dependencies.

## Where the brief, the DAG or earlier work was wrong

The rework table still records this module as quarantined, but its current source is
present at the assigned Lean path. This delivery uses that current source and preserves
its declarations and attachment; it withdraws no archive or module.

The three helper docstrings already point to the exact uniqueness specifications that
prove them. Their object clauses suffice directly, without a new intermediate theorem.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
