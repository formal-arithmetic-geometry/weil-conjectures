## What changed

The assigned theorem is proved by two strict coefficient-only steps. The new
`VectorIntegrationRestrictedChartCoefficientCore` module supplies the affine
tower unit base-change recursion as an ordered Tate descent comparison. The new
`VectorIntegrationRestrictedChartCoefficientComposition` module supplies the
inverse-frame and pasted-square composition after that descent expression is
substituted. The assigned module expands the two definitions, applies the core
comparison, and closes the result with the composition theorem and categorical
normalization.

## Proved and sorry left

Closed:

- `AlgebraicGeometry.Etale.vectorIntegration_restricted_chart_coefficient`.

Two named intermediate theorems remain as `sorry`, each in its own module:

- `AlgebraicGeometry.Etale.affineTraceRightBaseChange_unit_coefficient`
  (`lem-amb-vector-integration-restricted-chart-coefficient-core`), the affine
  tower coefficient recursion without a vector bundle or frame;
- `AlgebraicGeometry.Etale.vectorIntegration_restricted_chart_coefficient_composition`
  (`lem-amb-vector-integration-restricted-chart-coefficient-composition`), the
  geometric inverse-image composition after the tower comparison is expanded.

## No longer needed

No declared proof dependency was removed. The delivered route uses the
coefficient recursion and inverse-image composition dependencies named by the
original node; no compact-support, exchange, counit or frame-change modules are
introduced.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled two independent canonical calculations into one
large coefficient equality. Splitting it at the affine tower unit comparison
makes the remaining composition a separate geometric step. The positivity
hypothesis `hN` remains in the assigned declaration but is unused by this pure
coefficient calculation.

## New nodes

`lem-amb-vector-integration-restricted-chart-coefficient-core` records the
ordered coefficient base-change recursion.

`lem-amb-vector-integration-restricted-chart-coefficient-composition` records
the inverse-frame and pasted-square composition after that recursion.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
