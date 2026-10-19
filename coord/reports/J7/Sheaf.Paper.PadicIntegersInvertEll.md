## What changed

Proved `AlgebraicGeometry.ProEtale.padicIntegers_invertEll` in
`Sheaf.Paper.PadicIntegersInvertEll`, with its original signature and all coefficient
constructions unchanged. Reused the existing regular localization telescope, scalar
invertibility and exact scalar extension. The colimit comparison preserves the unit
by its zeroth leg; preservation of multiplication is proved by the telescope universal
property in each tensor factor. Added two fully proved private helpers for transporting
the telescope and detecting maps by their zeroth leg. Updated the node proof and
dependencies to match the proof. The notation-only namespace command change is
recorded in `coord/changes/J7-padic-invert-ell-proof-scope.md`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.padicIntegers_invertEll`
(node `det-prop-sfb-qlbar-colimit-x-invert-ell`).
Added 0 holes; 0 split-offs; 0 holes remain in the delivered module.
Both private helpers are proved. No existing statements or definitions were changed.

## No longer needed

Removed direct imports of `Sheaf.Topology.ProfiniteCondensedRing`,
`Sheaf.AlgebraicGeometry.ProEtalePointPullback`,
`Sheaf.CategoryTheory.SheafTensor`, `Sheaf.Algebra.Homology.FilteredColimitsTensor`,
and `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`.
Their corresponding proof dependencies `sk-def-sfb-pullback-from-point`,
`sk-def-sfb-sheaf-tensor`, `lem-pc-module-filtered-colimits-tensor`, and
`lem-weil-pbc-filtered-colimits-commute-finite-limits` need no direct invocation:
the already proved telescope and exactness results provide these steps.
The proof also does not separately invoke `sk-def-sfb-condensed-ring`,
`def-sfb-integers-to-subfield-point` or `def-weil-pbc-proetale-site` as proof
lemmas; their constructions remain in the unchanged statement and reused results.
Removed the obsolete direct tool-use entry for
`lem-pc-module-filtered-colimits-tensor`; the existing scalar-exactness proof
supplies flatness instead. No blueprint unit step is bypassed.
The unit's inversion step is exactly the theorem proved here.

## Where the brief, the DAG or earlier work was wrong

The DAG planned to rebuild the compact-denominator telescope and its exactness,
but the library already proves these for the same continuous coefficient objects.
The finite intermediate field's induced norm makes the presentations definitionally
agree. No false statement or definition repair was found. The arbitrary colimit's
ring structure is handled directly; no equality between its given module action and
its ring multiplication is assumed. Invertibility of the target scalar and the
colimit property suffice to detect multiplication in each factor.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
