## What changed

Replaced the sole proof hole in
`CategoryTheory.Adjunction.square_shift_mate` by the five-step argument in
`lem-weil-pbc-adjunction-square-shift-mate`. Naturality and the unprimed unit
compatibility give the comparison identity. The adjunction inverse formula,
target naturality, and primed counit compatibility give the two adjunct
formulas. Cancellation and injectivity then give the mate equation.

The theorem signature and public imports are unchanged. No other module changes.

## Proved and sorry left

Closed one hole: `CategoryTheory.Adjunction.square_shift_mate`
(node `lem-weil-pbc-adjunction-square-shift-mate`). No holes added, none split
off, and no `sorry` left in the delivered module.

## No longer needed

None. No imports removed and no nodes or modules pruned. All three declared
proof dependencies are Mathlib leaves used by the argument; the existing
imports already provide them. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The existing proof plan applies with the stated hypotheses. Only the
specified shift comparisons are cancelled; no invertibility of the comparison
transformation or its mate is assumed.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
