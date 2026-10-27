## What changed

`Sheaf.Paper.DiagonalDncChartNormalization.chartNormal_vectorPurity_normalization`
is reduced to source-etale restriction and the independent vector-bundle integration
model calculation. The proof transports the chosen ordinary orientation along the
actual projection equation, cancels its forward map, and substitutes the bundle
integration adjunct. The new private helper `chartOrdinaryOrientation_inv_congr`
proves equality transport directly; `chart_inverse_square` supplies the categorical
inverse-arrow calculation and postcomposition. The private helper
`chart_smooth_precomp_iso` obtains source-isomorphism invariance by composing
relative dimensions zero and d. All existing public signatures are unchanged.
The sole new proof import is `Sheaf.Paper.VectorBundleIntegrationOrientation`.
The new module imports only the existing diagonal-dualizing data; its reexports
already supply vector-bundle integration and the zero-section definitions.

## Proved and sorry left

One of the seven original holes is closed by decomposition:
`WeilConjectures.PurityFiniteSetting.chartNormal_vectorPurity_normalization`.
One lower hole is added:
`WeilConjectures.PurityFiniteSetting.vectorBundleIntegration_orientation_inv`
(node `lem-pur-vector-bundle-integration-orientation`). This is a decomposition,
not a net hole reduction: six holes remain in the item and one in the new module.
The private equality-transport helper and the categorical inverse-square helper
`chart_inverse_square` are fully proved. Smoothness is transported along the
presentation equation by a direct equality cast, rather than rewriting its
expanded normal-cone projection. The new proof respects transparency.

The six untouched holes, all attached to
`lem-pur-diagonal-dnc-chart-normalization`, are:

- `WeilConjectures.PurityFiniteSetting.diagonal_dnc_chart_normalization`;
- `WeilConjectures.PurityFiniteSetting.chartOrientation_etale_restriction`;
- `WeilConjectures.PurityFiniteSetting.chartOrientation_open_baseChange`;
- `WeilConjectures.PurityFiniteSetting.chartGamma_eq_inverseOrientation`;
- `WeilConjectures.PurityFiniteSetting.chartEpsilon_standing_composition`;
- `WeilConjectures.PurityFiniteSetting.chartDiagonalDelta_coordinate_identity`.

Validation: the new module compiled cleanly through `lcompile.py --all`
(37.4 seconds), and again in the delivery check (46.3 seconds). The initial item
proof compiled in 52.2 seconds but a delivery recompile exceeded the 60-second
limit; no push occurred. Profiling identified a 28-second smoothness-instance
conversion. It has been replaced with the direct equality cast described above;
the optimized proof compiled successfully in 54.1 seconds. The final proof also
uses explicit zero-plus-d smooth composition and a generic categorical
postcomposition calculation, and has no transparency overrides. Profiling
options were removed before the delivery compilation and preflight.

## No longer needed

No existing import, node or module is withdrawn. The new lower theorem isolates
the vector-bundle model portion of the chart proof; it does not use normal-cone
geometry, a coordinate presentation of that cone, or the standing exceptional
composition comparison. Those arguments remain necessary for other item clauses. The normal-cone
subproof no longer uses `chartOrientation_coordinate_formula` or
`chartGamma_counit_normalization`; those declarations stay for the coordinate
clauses, so this removes no library module from the target closure.

## Where the brief, the DAG or earlier work was wrong

The available `vectorBundleDiagonalOrientation` theorem requires
`P.extension = bottom`. The item allows arbitrary finite coefficient extensions,
so that theorem cannot discharge its bundle normalization directly. The new lemma
states just the ordinary integration model needed here at the item's coefficient
range. Blueprint searches for vector-bundle orientation found the bottom-extension
orientation theorem and the existing general-ring purity package; neither states
this normalized ordinary bundle calculation in a usable form.

The new statement was checked on rank zero, the empty affine scheme, and arbitrary
finite coefficient extensions. The identity ordered trace handles rank zero; the
empty cover gives uniqueness on the empty scheme. It imposes no extra hypothesis
on the original theorem and does not select data from a mere existence statement.

## New nodes

`lem-pur-vector-bundle-integration-orientation`, realized by
`Sheaf.Paper.VectorBundleIntegrationOrientation`, is the bundle-model subcalculation
of chart proof Step 4. It compares any coordinate-counit-normalized ordinary
orientation with the actual integration adjunct on an affine base. It contains
no normal cone or map presenting one. The item proof supplies the separate etale
restriction and projection-equality transport, so the lower theorem is strictly
part of the argument. Its source, proof, search records and Lean signature are in
the node. No change records are needed because no existing interface changes.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
