## What changed

Completed `AlgebraicGeometry.ProEtale.AffineLineEvaluation.exceptionalInput` and
`AlgebraicGeometry.ProEtale.AffineLineEvaluation.evaluation_naturality` in
`Sheaf.Paper.AffineLineCompositeTranspose`. Existing public signatures and
non-theorem constructions are unchanged. Fully proved private helpers package the
canonical projection as a natural transformation, invert its naturality square,
and commute tensor integration with the coefficient right unitor.

For exceptional admissibility, the comparison adjunction unit identifies the given
ordinary etale representative with `Rnu_* K`. Ordinary etale exceptional
preservation then applies directly, using the positive invertible coefficient
exponent already supplied by the purity setting. The node's first proof step now
records this shorter route. Step 2 follows the existing plan.

## Proved and sorry left

Closed 2 of the original 4 holes:

- `AlgebraicGeometry.ProEtale.AffineLineEvaluation.exceptionalInput`.
- `AlgebraicGeometry.ProEtale.AffineLineEvaluation.evaluation_naturality`.

Added 0 holes; split off 0 statements. The following original holes remain,
all attached to `lem-pur-affine-line-composite-transpose`:

- `AlgebraicGeometry.ProEtale.AffineLineEvaluation.evaluation_unit`.
- `AlgebraicGeometry.ProEtale.AffineLineEvaluation.composite_transpose`.

This is a partial proof delivery, not a decomposition. The proved helpers contain
no holes. Compilation and delivery checks are run through the launcher tools.

## No longer needed

Removed the following private imports:

- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`.
- `Sheaf.SixFunctors.OpenTensorNormalization`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`.
- `Sheaf.Paper.ProjectionMateExact`.
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`.
- `Sheaf.Paper.SfPreservationClass`.

Five of these are already reexported by the unchanged public imports. The open
normalization and projection-mate imports are not used by either completed proof;
they belong to the remaining unit-normalization plan. Their nodes remain in the
DAG for that unfinished argument. `thm-sf-preservation-class` is no longer needed
for Step 1: ordinary etale exceptional preservation proves the actual antecedent
claim directly. Removed its proof-dependency and top-level tool-use entries.
No module is withdrawn, and no module is claimed to leave the target closure.

## Where the brief, the DAG or earlier work was wrong

No statement change or disputed statement. The preservation plan was longer than
necessary for the recorded ordinary antecedent: the existing ordinary source
API fits it directly. The composite proof still requires compatibility of the
chart's specified Hom chain with the standing exceptional counit and canonical
change of compactification. Having the same objects does not establish this
compatibility. The existing `compactSupportComparisonNormalization` identifies
the fixed comparison with `compactSupportSiteComparison`; further comparison with
the upstream compact-support comparison, and the right-adjoint transport, remains
unfinished here. The original named composite hole is retained unchanged.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
