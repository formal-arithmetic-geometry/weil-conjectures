## What changed

Filled `CochainComplex.projective_top_cell_attachment` in
`Sheaf.Paper.ProjectiveTopCellAttachment`, preserving its statement, docstrings and imports.
The proof follows the existing five-step plan. Bounded projectivity gives a chain-map
representative via Mathlib's K-projective bijection and the full homotopy quotient.
Two rotations and `isoTriangleOfIso₁₂` identify its shifted cone with the given middle
object. The cone projections and inclusions give the prescribed term isomorphisms;
the shifted projection cocycle gives the lower differential identity, and the cone
differential formula gives the top differential identity.

For the positive-sign presentation, the same underlying complex is used with its
top-term identification negated. This satisfies every specified comparison equation.
For finite freeness, the first cone projection identifies every degree other than
`b` with the corresponding term of `K`, including degrees above `b`; degree `b`
is identified with `P`. No separate rank-zero freeness lemma is needed.

## Proved and sorry left

Closed the sole original hole in `CochainComplex.projective_top_cell_attachment`
(blueprint: `lem-sf-projective-top-cell-attachment`). Holes closed: 1. Holes added: 0.
No remaining `sorry` and no split-off statements.

## No longer needed

None. No imports, modules or declared DAG dependencies were removed. The existing
Mathlib representative, derived-category, triangulated-category and triangle-isomorphism
dependencies all participate in the proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing statement allows the positive-sign
presentation to share the underlying complex with the negative-sign presentation:
negating the top identification alone expresses the indicated coordinate change.
The construction and projection inverses include `P = 0`, `K = 0`, adjacent bounds,
and arbitrary integral bounds.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
