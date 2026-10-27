## What changed

Added two genuine intermediate theorem modules for the affine descent construction:
`SymmetricProjAffineComparisonExistence` isolates existence of the affine twist
comparison and its chart equation, while `SymmetricProjSectionCompatibility`
isolates the degree-one section formula. The assigned theorem now combines these
interfaces into `NormalizedAffineRestriction` with a complete Lean proof. The new
intermediate proofs remain explicitly named `sorry`s with source and proof text in
their docstrings. No definitions contain `sorry` and no existing target signature
was changed.

## Proved and sorry left

The original theorem
`AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_normalized_quotient_with_affine_restriction`
is proved by assembling the two strictly smaller intermediate statements.
Two split-off holes remain:

- `AlgebraicGeometry.SymmetricProjTautologicalCharts.exists_affine_comparison_with_chart_compatibility`
  in `lem-trf-symmetric-proj-affine-comparison`.
- `AlgebraicGeometry.SymmetricProjTautologicalCharts.section_compatibility_of_affine_comparison`
  in `lem-trf-symmetric-proj-section-compatibility`.

## No longer needed

No imports or nodes were pruned. The original construction dependencies are represented
by the two split theorem interfaces and remain available for their future proofs.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the affine comparison, its chart normalization, and
its degree-one section calculation into one large existence theorem. These are
independent source steps; naming them separately gives a real assembly proof while
preserving the exact target statement and all its hypotheses.

## New nodes

- `lem-trf-symmetric-proj-affine-comparison`: affine twist comparison with chart
  compatibility, source Tags 01NR and 01OB.
- `lem-trf-symmetric-proj-section-compatibility`: degree-one section compatibility
  for that comparison, source Tags 01NR, 01OB and 01N2.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
