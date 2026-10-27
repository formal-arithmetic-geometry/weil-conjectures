## What changed

Proved `ContinuousCohomology.exists_jointContinuousCoordinateDifferential` without
changing its statement. The proof constructs the continuous equivariant and
continuous function submodules with their exact membership predicates, then
constructs all four linear maps by the prescribed pointwise formulas.
Continuity of the cumulative-product map is proved by finite induction.
Continuity of each differential follows from coordinate projections, continuous
multiplication and the jointly continuous action. Equivariance and linearity
follow pointwise.

The omission square is expanded and regrouped using
`Fin.sum_sum_eq_sum_triangle_add`; the two deletion orders agree by
`Fin.succAbove_succAbove_succAbove_predAbove` and their signs cancel. The first
face uses `Fin.partialProd_succ'` and equivariance; the internal faces use
`Fin.partialProd_contractNth`; the final face uses `Fin.partialProd_init`.
These identities yield the chain-map comparison by separating the zero-index
summand. The degree-zero formula is checked using uniqueness of the empty tuple.

Added only a private proof import of `Mathlib.Tactic.FunProp` and two proved
private helpers in the assigned module. The original public imports, theorem
signature and DAG proof route are preserved.

## Proved and sorry left

Closed the sole original hole:
`ContinuousCohomology.exists_jointContinuousCoordinateDifferential`
(node `lem-sfb-joint-continuous-coordinate-differential`).

Holes closed: 1. Holes added: 0. Sorries remaining: none. Split-off statements: none.

## No longer needed

None. There were no project proof dependencies or private proof imports to
remove. All original public imports are retained. No DAG nodes or project
modules are bypassed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The proof implements the eight existing DAG
steps directly using elementary Mathlib identities and preserves the unit route.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
