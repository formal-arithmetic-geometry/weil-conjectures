## What changed

Filled `AlgebraicGeometry.Etale.sheafHDerivedEquiv_symm_restriction` in
`Sheaf.AlgebraicGeometry.SheafHDerivedPullback`. The statement is unchanged.
The proof first compares forward fixed evaluation with Ext pullback. It uses the
existing proved shift transport, derived-unit normalization and constant-sheaf
adjunction comparisons, then coefficient naturality and inverse cancellation.
The generic evaluation-pullback lemma keeps the derived constructions abstract
until specialization to sheaves. All added mathematical helpers are private and proved.
A local instance priority selects the abelian category's additive structure
consistently, avoiding repeated conversion against the full-subcategory structure.
The final module compiled cleanly in 51.7 seconds, with no warnings.
No definitions are changed.
All added imports are proof imports.
The node records these proof steps and the existing helper dependencies explicitly.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.sheafHDerivedEquiv_symm_restriction`
(node `lem-weil-pbc-sheaf-h-derived-pullback`). No holes added or split off.
There are no remaining `sorry` declarations in this delivery.

## No longer needed

None. Every original declared dependency remains used. No original imports,
nodes, modules, unit statements or unit proof steps are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The previously unstated glue is proved
locally from the existing derived-unit and shift-transport results; no further
split of the pullback obligation is necessary. The proof works for arbitrary
scheme maps before specializing to chart maps, so it imposes no extra hypotheses
on degree zero, identity maps, zero coefficients or empty schemes.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
