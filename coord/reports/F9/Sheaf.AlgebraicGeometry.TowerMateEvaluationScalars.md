## What changed

Filled `evaluation_open_unit` using generic exact localization of the termwise
open unit equation. The proved private helpers `derived_refl_iso`,
`exact_evaluation_unit`, and `exactAdj_dJAdj` normalize the specified comparisons
and adjunctions without repeatedly unfolding their constructions.

Filled `scalarJInv_app_isIso` by transporting the scalar open mate through the
fixed-coefficient coordinate equivalences. This uses the arbitrary-ring private
helpers of `FiniteOpenExchangeScalars` and `FiniteConstantCoefficientTransport`;
no finiteness assumption is introduced.

Existing public signatures, definitions, attributes, and imports are unchanged.
The two child nodes now record the completed proofs, and the parent plan records
their use.

## Proved and sorry left

Closed two of the four original holes, both in
`AlgebraicGeometry.ProEtale.StrictTower.MateEvaluationScalars`:

- `evaluation_open_unit` (lem-cbc-tower-mate-evaluation-open-unit).
- `scalarJInv_app_isIso` (lem-cbc-tower-mate-scalar-jinv-app-is-iso).

The original holes `scalar_alpha` and `scalar_gamma` remain, both attached to
lem-cbc-tower-mate-evaluation-scalars. No holes were added or split off.

## No longer needed

No imports, nodes, or modules are removed. The original scalar alpha/gamma route
and its dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

The finite-ring theorem `FiniteOpenScalars.openResMap_isIso` has a proof using
only arbitrary-ring private helpers. Its argument therefore proves this item's
arbitrary-ring component invertibility without another theorem with `sorry`.
The child nodes previously had empty proof plans; their plans now record the
proofs written here. No statement or definition repair was necessary.

An attempted scalar gamma reduction through exact descent of the ordinary alpha
cube exceeded the required kernel-checking limit and is not included. The two
original scalar obligations remain unchanged.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
