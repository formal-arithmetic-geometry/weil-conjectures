## What changed

Updated `lean/Sheaf/Paper/RingedProjectionRestriction.lean`. The main theorem now
has a complete Lean proof that combines three named intermediate results. Added
three public theorem declarations, each carrying its own source and blueprint
reference, for the global normalized construction, local slice compatibility, and
local detection argument. Added the corresponding DAG node records and updated the
item node's proof and proof dependencies to match this route.

## Proved and sorry left

The original `ringedProjectionRestriction` hole is closed by existential elimination
and conjunction introduction. Three genuinely separate proof obligations remain as
named theorem holes: `ringedProjectionRestriction_global`,
`ringedProjectionRestriction_local`, and `ringedProjectionRestriction_detection`.
Their node records are, respectively,
`lem-weil-pbc-ringed-projection-restriction-global`,
`lem-weil-pbc-ringed-projection-restriction-local`, and
`lem-weil-pbc-ringed-projection-restriction-detection`.

## No longer needed

No imports were removed. The original proof dependencies are retained by the three
new node routes; no module or DAG dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The existing seven-step plan was mathematically appropriate but too large for one
Lean proof obligation. The delivery makes its three independent stages explicit;
no target statement or definition was changed.

## New nodes

`lem-weil-pbc-ringed-projection-restriction-global` records existence of the
normalized global operation, derived adjunction, and signed tensor data.

`lem-weil-pbc-ringed-projection-restriction-local` records existence of all local
slice comparisons and their projection compatibility for a fixed global datum.

`lem-weil-pbc-ringed-projection-restriction-detection` records the covering-sieve
criterion that local slice isomorphisms detect a global derived isomorphism.

The interface change record is
`coord/changes/ringed-projection-restriction-splits.md`.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
