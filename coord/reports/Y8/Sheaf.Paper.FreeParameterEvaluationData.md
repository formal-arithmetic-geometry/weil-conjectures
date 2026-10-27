## What changed

Filled `AlgebraicGeometry.ProEtale.FreeParameterEvaluation.universalSection_compatible`
in `Sheaf.Paper.FreeParameterEvaluationData`. After identifying section-module restriction
with the underlying abelian presheaf restriction, functoriality combines the two maps.
The over-category morphism equation identifies the resulting composite with restriction
along the terminal arrow. This is precisely the argument in the existing docstring.
All signatures, definitions and imports are unchanged.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.ProEtale.FreeParameterEvaluation.universalSection_compatible`
(node `def-sfb-free-parameter-evaluation-data`).
One of one original holes proved; zero holes added, zero split off, zero holes remain
in the delivered module. No new intermediate declarations or theorem dependencies.

## No longer needed

None. All three public imports remain needed for the recorded definitions and instances.
No DAG dependencies, nodes or modules are withdrawn. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing docstring already describes the elementary
presheaf-functoriality proof; no derived evaluation coherence result is needed for this
restriction compatibility.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
