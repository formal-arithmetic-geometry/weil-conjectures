## What changed

Proved `AlgebraicGeometry.Scheme.Modules.affineRealizationComparison_pullback`
from the existing normalized comparison pullback square. The proof establishes
compactness and separatedness of both affine-chart fibre products, specializes
the uniquely normalized comparison family, and composes the proved comparison
and restriction equations. It follows the existing unit route.

Names for the actual chart arrow, tensor-composition coefficient map, universal
section formula and cohomology pullback composite keep conversions small.
Their defining equations and the section-formula equivalence prove that the
revised interface states exactly the original square. Existing comparison and
restriction definitions remain verbatim. Adapted the sole consumer,
`Sheaf.AlgebraicGeometry.AffineCohomologyRawRestriction`, preserving both public
signatures. Its proof composes the typed raw-evaluation equation with the square.
No target statement or adopted source-library declaration changes.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.Modules.affineRealizationComparison_pullback`.
Added zero holes. No `sorry` remains in any delivered module. All auxiliary
statements are proved, including `affineRealizationRestriction_apply`, both
chosen-comparison equations, normalization of the named comparison family,
the coefficient-map equations, the section-formula equivalence and congruence,
the cohomology-map evaluation equation, and the typed raw-evaluation equation.
This is a proof from existing project declarations, not a decomposition into
new unproved obligations. The existing raw-restriction consumer stays proved.

## No longer needed

The route no longer needs
`lem-weil-pbc-affine-raw-evaluation-pullback`, or its module
`Sheaf.AlgebraicGeometry.AffineRawEvaluationPullback`. The consumer was its sole
Lean importer and sole DAG citer; this delivery replaces that dependency by the
typed raw-evaluation equation. The old proved declaration and source file are
preserved. The new equation uses the original proof's generic coefficient
composition, derived evaluation, normalization and unit-evaluation components
directly. No original public import is removed. The original normalized
comparison square and affine comparison-data nodes remain needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. Inferring the chart arrow through
comma-category objects while using coefficients on actual fibre-product
schemes made the original presentation hard to elaborate with transparency
respected. Large implicit conversions also exceeded the kernel time limit.
The typed maps, proposition structure, explicit coefficient equations and
generic coefficient and equality-substitution proofs preserve all original quantifiers and constructions.
The square is specialized at explicit fibre-product schemes before its
comparison functions and pointwise equations are supplied. Empty charts,
zero coefficients, identity arrows and degree zero require no exception.
The change record is `coord/changes/A4-affine-comparison-typed-maps.md`.

## New nodes

`def-weil-pbc-affine-pullback-coefficient-map`, in
`Sheaf.AlgebraicGeometry.AffinePullbackCoefficientMap`, constructs the induced
chart arrow and original tensor-composition coefficient map. Its proved
equations identify the named transport with the direct `congrArg` transport.

`def-weil-pbc-coherent-etale-pullback-data`, in
`Sheaf.AlgebraicGeometry.CoherentEtalePullbackData`, constructs the cohomology
composite and stores exactly the original universal section formula. Its
projection, constructor, equivalence, coefficient congruence and evaluation
equation are proved.

`def-weil-pbc-affine-normalized-comparison-family`, in
`Sheaf.AlgebraicGeometry.AffineNormalizedComparisonFamily`, names the existing
uniquely normalized family and proves its normalization. The uniqueness
statement determines the chosen object; no arbitrary existence witness is used.

`lem-weil-pbc-affine-comparison-chosen-equality`, in
`Sheaf.AlgebraicGeometry.AffineComparisonChosenEquality`, proves both the
inverse-choice and inverse-named-family equations for the unchanged comparison.

`lem-weil-pbc-affine-restriction-equation`, in
`Sheaf.AlgebraicGeometry.AffineRestrictionEquation`, proves the pointwise
restriction equation by the original construction and coefficient-map equality.

`lem-weil-pbc-affine-raw-evaluation-typed-pullback`, in
`Sheaf.AlgebraicGeometry.AffineRawEvaluationTypedPullback`, proves raw restriction
evaluation in the typed interface from the original generic coefficient
composition, derived evaluation, normalization and unit-evaluation components.
Keeping the section conversion generic avoids the expensive implicit
conversions in an application of the old expanded theorem. It uses no normalized
ordinary comparison or additional geometric hypothesis.
All six node files are under `dag/nodes/sec-proper-base-change/`.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
