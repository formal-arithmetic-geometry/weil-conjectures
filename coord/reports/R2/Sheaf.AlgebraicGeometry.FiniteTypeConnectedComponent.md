## What changed

Filled the proof of
`AlgebraicGeometry.finiteType_connectedComponent_open_quasiCompact` in
`Sheaf.AlgebraicGeometry.FiniteTypeConnectedComponent` without changing its statement,
docstrings, definitions, or imports. The proof follows the existing five-step node:
Mathlib gives local Noetherianity and compactness of C; together these give
Noetherianity. The source-library component-openness theorem defines the required
open subscheme. Every subset of C is compact, and the connected component is
connected as a subspace. The existing instances give local finite type and
quasi-compactness of the open immersion and then of its composite with the
structure map. No other module or node is changed. The remote single-file compile passed
without diagnostics in 2.0 seconds.

## Proved and sorry left

Closed the single existing hole in
`AlgebraicGeometry.finiteType_connectedComponent_open_quasiCompact`
(node `lem-trf-finite-type-component-open-qc`). Holes closed: 1. Holes added: 0.
No sorry remains in the item, and no split-off statement is introduced.

## No longer needed

None. No imports, nodes, or modules are pruned. The existing DAG route and all its
mathematical ingredients are retained, using their already available Mathlib and
source-library declarations. No additional proof-dependency import is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing source-library and Mathlib
APIs already supply all five steps. The proof needs neither smoothness nor
separatedness. Empty C is vacuous because c : C is an input; the singleton,
nonreduced, disconnected, and nonseparated cases do not require any extra
hypothesis. No unit route is bypassed.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
