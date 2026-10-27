## What changed

Filled the proofs of `AlgebraicGeometry.ProEtale.StrictTower.supportExchange_id` and
`AlgebraicGeometry.ProEtale.StrictTower.supportExchange_comp` in the assigned module.
All existing declaration signatures and docstrings are unchanged.

The proof follows the node's four steps. Two proved private helpers take the normalized
pullback-square identity and horizontal pasting laws to their proper-adjunction mates.
The main proofs combine those equalities with `beta_id` and `beta_comp`. Functoriality
cancels the ambient inverse-image compositors, and naturality of the second proper
exchange moves the first open comparison through it. Equality is proved on components
of natural transformations in the unbounded derived strict-tower categories.

Two additional private helpers handle inverse cancellation and perform the two-factor calculation for abstract functors, so that
the kernel can check the calculation without reducing the concrete localization construction.
The final file compiles cleanly through `lcompile.py` in 7.8 seconds.

Added proof imports of the upstream mate-whiskering API and the private identity-square
calculation already proved in `StrictTowerProperOpenCalculus`. No construction, statement,
public import, node route, or consumer is changed.

## Proved and sorry left

Closed 2 of the original 2 holes:

- `AlgebraicGeometry.ProEtale.StrictTower.supportExchange_id`.
- `AlgebraicGeometry.ProEtale.StrictTower.supportExchange_comp` (both conjuncts).

Both realize `lem-cbc-strict-support-horizontal-exchange`.
No holes remain in the item, no holes are added elsewhere, and no statements are split off.
All four private helpers are proved in full.

## No longer needed

None. The proof follows the existing DAG plan and uses its pullback-square pasting,
normalized proper/open calculus, strict-tower operations and mate-calculus dependencies.
No imports, nodes or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The proof does not use finite origin,
boundedness, completeness, invertibility of proper exchange, or faithfulness of evaluation.
The latest blueprint now formulates the parent compact-support theorem using condensed
coefficients; the assigned strict-tower coherence statements themselves are unchanged
and the present proof verifies exactly those existing statements.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
