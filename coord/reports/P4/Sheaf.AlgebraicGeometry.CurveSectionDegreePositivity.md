## What changed

Proved `AlgebraicGeometry.Scheme.Modules.curve_section_degree_nonneg_and_pos` in
`Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity`, preserving its complete signature.
The proof constructs the effective Cartier zero ideal, identifies the original line bundle
with its dual ideal, and computes its degree by closed-subscheme Euler additivity, affine
vanishing, and the existing finite-scheme h-zero calculation. Nonemptiness of the zero scheme
then gives strict positivity via a germ map and `Module.finrank_pos`.

Added private proof imports of `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch` and
`WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus`; updated the proof docstring
and the item's DAG proof/dependencies to the actual argument. No definition, statement,
public import, adopted-source file, or consumer changed. The unit's realized route is retained.

Validation: the single-file server compile succeeds without errors or warnings. Edge cases
are covered: an empty zero scheme has rank zero and gives only nonnegativity; a proper
nonvanishing locus forces a point of the zero scheme; no smoothness or rational-point
hypothesis is introduced.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.Modules.curve_section_degree_nonneg_and_pos`
(node `lem-trf-curve-section-degree-positivity`).
Added 0 holes; split off 0 statements. There are 0 sorries left in the delivered module.
The proof uses existing declarations, including the already stated
`AlgebraicGeometry.effectiveCartierDivisor_finite_over_field`; it does not claim their
transitive sorry dependencies are closed.

## No longer needed

Removed private imports `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme`,
`WeilConjectures.AlgebraicGeometry.Dimension`, and
`WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`. The latter two remain available
through the modules actually used. The full Picard zero-scheme dictionary is unnecessary;
the general section nonvanishing/support comparison suffices.

The item no longer needs node `lem-pc-zero-scheme-properties`, whose recorded theorem is
about the Picard dictionary, or node `lem-pc-degree-base-change`: its recorded effective
Cartier degree theorem requires smoothness. The proof instead computes the degree from
general Euler additivity and finite-scheme cohomology. Removed that obsolete top-level
`tool_uses` entry as well. No module is withdrawn; other consumers may still need these nodes.

## Where the brief, the DAG or earlier work was wrong

The old step 3 described a general proper dimension-at-most-one effective-divisor degree
formula as available from `lem-pc-degree-base-change`. Its recorded declaration
`IdealSheafData.IsInvertible.degree_dual_toModules` is actually in
`WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`, not the recorded EulerChar module,
and requires `SmoothOfRelativeDimension 1`. It cannot be applied to the present integral
curve. The packet proves the needed formula using `eulerChar_tensorObj_eq_add` and the
finite-scheme results, which have no smoothness hypothesis. The old step 1's Picard
zero-scheme-properties attachment also does not supply the general support comparison;
use the existing exact node `lem-weil-pbc-section-nonvanishing-zero-locus` instead.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
