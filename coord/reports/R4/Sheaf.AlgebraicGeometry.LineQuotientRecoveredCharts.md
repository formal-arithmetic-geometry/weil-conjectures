## What changed

Replaced the proof hole in `lineQuotient_recovered_charts` by an explicit reduction to
`lineQuotient_pulled_chart_normalization`, a new local degree-one calculation in
`Sheaf.AlgebraicGeometry.LineQuotientPulledChartNormalization`.

The item constructs the coefficient ring homomorphism using the existing fraction-atlas
coefficient API. Induction on the powers of the symmetric generator submodule proves the
all-degree fraction equation. Separate proved helpers compare the localized chart maps,
produce an affine generator chart near every source point, and glue the comparison to
identify the recovered morphism with the given morphism. Existence and uniqueness of the
graded extension and its full chart data are reused from the existing homogeneous-fraction
map theorem. All existing public signatures and definitions are preserved.

## Proved and sorry left

Closed the item's original direct hole in
`AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_recovered_charts`.
The item has zero direct holes. Added one direct hole:
`AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_pulled_chart_normalization`
(node `lem-trf-line-quotient-pulled-chart-normalization`). This is a decomposition,
with one hole closed and one added, not a net hole closure. The remaining theorem asserts
only the free frame, scalar equation and degree-one quotient equation on one affine
standard chart. It mentions neither a graded extension nor higher-degree coefficients
nor a global chart predicate. Every higher-degree and global comparison step is proved
in the item module.

Validation: both modules compile on the server: the new local lemma in 17.1 seconds
and the item in 16.3 seconds, below the 60-second limit. The final line-length warning
was fixed by wrapping a simp list. Existing theorem signatures match the repository
verbatim after whitespace normalization; the new node signature matches its declaration,
and each node proof-dependency list equals the union of its proof steps. The delivery
command reruns compilation and preflight on the final files.

## No longer needed

No existing import was removed and no module is withdrawn. The original proof dependencies
`lem-weil-pbc-invertible-pullback-invertible`,
`lem-pc-module-pullback-identity-composition`,
`lem-weil-pbc-module-pullback-affine-sections`, and
`def-weil-pbc-proj-twisting-sheaf` are not direct inputs of the assembled proof.
The first is replaced by the existing explicit tensor-pullback preservation theorem;
composition and twisting-sheaf normalization remain dependencies of the new local lemma.
The affine tensor-section isomorphism is not needed by the all-degree induction or chart
comparison. The datum definition remains a statement dependency and is used through its
line invertibility and quotient epimorphism. No global claim of module pruning is made.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies state the quotient datum, twists, affine pullback isomorphisms,
and existence of a fraction-chart morphism, but do not directly state the transport of the
normalized tautological quotient into an arbitrary pulled affine chart. That precise
local degree-one bridge is the remaining named obligation. Its scalar equation and free
frame are retained explicitly so that the proof applies to zero rings and empty charts.
No statement is disputed or weakened, and the unit route is preserved.

## New nodes

`lem-trf-line-quotient-pulled-chart-normalization` records the local frame, structural
scalar and degree-one quotient equations of the pulled normalized tautological quotient.
Its source is Stacks Constructions, Tags 01OA and 01O4. The theorem's docstring and node
spell out the chart-twist calculation and its transport through the section-normalized
tensor pullback comparison. The new node inherits the item's chapter, unit and blueprint
ancestry. There are no change records because no existing interface changes.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
