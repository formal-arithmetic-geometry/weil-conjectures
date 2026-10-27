## What changed

Restored `lean/Sheaf/Paper/FiniteReductionSystemCoherence.lean` from its quarantine
archive and repaired the ordinary comparison-associator proof. Use explicit
isomorphism cancellation rather than synthesizing mono/epi instances for the
components of the sheaf associators. Unfold the mapped inverse explicitly during
simplification. The public declaration `AlgebraicGeometry.FiniteReduction.System.coherentAt`,
its signature, all imports, and its three-step argument are preserved.

Validation: the final sandbox module compiled through `lcompile.py` with exit code 0,
no errors or warnings, in 47.7 seconds.

Change record: `coord/changes/finite-reduction-system-coherence-cancellation.md`.

## Proved and sorry left

This is a zero-hole compile repair. The archive has zero `sorry`s; the restored
module has zero `sorry`s. Holes closed: none (0 of 0). Holes added: none.
`AlgebraicGeometry.FiniteReduction.System.coherentAt` remains proved by the
ordinary adjunction-pasting square, computation on common flat K-flat resolutions,
and naturality transport to arbitrary derived objects.

## No longer needed

None. No imports, declarations, modules, or DAG dependencies are removed.
The node `lem-pur-finite-reduction-system-coherence` still describes exactly the
proof and retains its Lean attachment. Its existing dependency modules
`FiniteReductionSystem` and `FiniteReductionFlatExtension` are used.

## Where the brief, the DAG or earlier work was wrong

The assigned module was absent from `lean/` because it was quarantined after the
upstream sync, not because its theorem was withdrawn. The unchanged archive
reproduced the reported universe constraint at generic associator cancellation:
`u + 1 =?= max (u + 2) ?u`. The mathematical statement and DAG route need no repair.
A search of both live and quarantined sources finds the quarantined consumer
`Sheaf.Paper.FiniteReductionSystemExistence`, whose final application of
`System.coherentAt` keeps exactly the same type. There are no live downstream modules
in `tools/downstream.py --allow-missing --uses`.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
