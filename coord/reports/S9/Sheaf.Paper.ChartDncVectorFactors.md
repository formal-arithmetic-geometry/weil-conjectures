## What changed

Proved five construction lemmas in `Sheaf.Paper.ChartDncVectorFactors` without changing
any declaration signature or definition. `sourceLift_geometry` identifies the intermediate
map as a base change of the chart map and derives separatedness and quasi-compactness by
cancellation. `idealCondition` uses functoriality of kernel ideal sheaves, and
`normalCondition` uses preservation of the deformation parameter.

For `normalGeometry`, restrict to the prescribed diagonal neighbourhood from
`ChartNormalDifferential.chartGeometry`. Flat Cartesian base change of the existing Rees
quotient gives the two normal comparisons. The comparison for the open inclusion is
invertible. A proved composition formula for the coefficientwise Rees maps, checked on a
cover by three compatible affine opens, identifies the resulting composite with the
existing `normalMap`. Cancellation gives its Cartesian square and zero-section equation.
The private helpers are all completely proved.

Added proof-only `import all` access to `Sheaf.Paper.SectionReesBaseChangeEtale` and
`Sheaf.Paper.ChartNormalDifferential`, reusing their proved private construction APIs.
Updated the existing node's proof and dependencies to record the section-Rees argument.
No public imports, definitions, signatures, target statements or consumers changed.

## Proved and sorry left

Closed five of the six original holes:

- `WeilConjectures.PurityFiniteSetting.ChartFactors.selfMap_fst`.
- `WeilConjectures.PurityFiniteSetting.ChartFactors.sourceLift_geometry`.
- `WeilConjectures.PurityFiniteSetting.ChartFactors.idealCondition`.
- `WeilConjectures.PurityFiniteSetting.ChartFactors.normalCondition`.
- `WeilConjectures.PurityFiniteSetting.ChartFactors.normalGeometry`.

One original hole remains, unchanged:
`WeilConjectures.PurityFiniteSetting.ChartFactors.chart_dnc_vector_factors`, owned by
`lem-pur-chart-dnc-vector-factors`. Its docstring retains the complete proof plan for
normalization and integration compatibility. This is a partial delivery of a module with
several holes, not a decomposition. Added holes: zero. Split off: zero.

## No longer needed

Removed unused proof imports:

- `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization`.
- `Sheaf.Paper.CohomologicalSmoothnessTheorem`.
- `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`.
- `Sheaf.AlgebraicGeometry.VectorTraceGeometricDescent`.

The final theorem is still open and its proof plan still needs the corresponding
mathematics. These import removals therefore do not withdraw any DAG dependency or
justify pruning any module. No modules or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The existing private section-Rees
API supplies the flat normal-cone base-change construction without Noetherian or smooth
hypotheses, which is needed for the general signature of `normalGeometry`. The actual
Rees zero-fibre map agrees by composition and cancellation with this construction.
Neither nonempty schemes nor positive relative dimension are used.

The remaining derived compatibility theorem has not been proved. An attempted separate
frame calculation used bundleOrientation_frames and naturality of pullComparison; its
unfolding exceeded the per-file compilation limit, so that unverified, unused helper is
excluded from this packet. The five delivered proofs do not depend on it.

## Second reading by S9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
