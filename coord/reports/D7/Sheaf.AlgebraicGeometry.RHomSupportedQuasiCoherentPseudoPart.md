## What changed

Reworked the existing proof of `AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part`
from a pair term to an explicit `constructor` proof. The theorem statement and its two
proof imports are unchanged. The resulting proof applies the existing quasi-coherence and
local lower-bound component theorems to the two conjuncts.

## Proved and sorry left

The item contained no `sorry` before this delivery. The declaration
`AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part` remains fully proved; no
`sorry` was closed and no `sorry` was added.

## No longer needed

None. The existing imports and DAG proof dependencies remain needed by the theorem proof.

## Where the brief, the DAG or earlier work was wrong

The assigned item was already proved in the repository, with no remaining `sorry` in its
module. No statement or dependency correction was necessary.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
