## What changed

Added `Sheaf.Paper.AdicExtensionCompCocycle`, which states the normalized derived scalar-extension associativity cocycle used to reduce `adicReduction_cocycle`. The assigned target module now imports this reduction theorem. Both declarations compile; the target proof remains a named `sorry` because conversion through the large quotient-reduction definitions exceeds the single-file kernel time limit.

## Proved and sorry left

- `AlgebraicGeometry.Scheme.adicReduction_cocycle`: sorry remains (the assigned hole).
- `AlgebraicGeometry.Scheme.adicFiniteExtensionComp_cocycle`: split off as a strictly more general scalar-extension cocycle; sorry remains for parallel proof.

## No longer needed

None. The existing `AdicFiniteReductionData` dependency is still required by both the target and the split theorem.

## Where the brief, the DAG or earlier work was wrong

The direct specialization is definitionally the abstract cocycle, but unfolding `adicFiniteRho`, `adicFiniteReduction`, and the derived extension comparisons during conversion exceeds the 60-second per-file kernel limit. The abstract theorem isolates the mathematically substantive coherence step and avoids changing the target statement.

## New nodes

- `lem-sfb-adic-extension-comp-cocycle`: normalized cocycle for three successive derived scalar extensions.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
