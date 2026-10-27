## What changed

Proved the ordinary orientation witness equation, affine-coordinate geometry,
coefficient-unit bounds and constructibility, affine-mate invertibility, coordinate
formulas, the normalized conormal/Rees model, differential frame, and its explicit
normal-coordinate map. All existing mathematical statements and constructions are
preserved. Proof imports expose the established differential and vector-bundle APIs.
Private proved helpers handle a pullback universal property and the polynomial
coordinates of a framed symmetric algebra. Explicit composition instances avoid
expensive searches in the existing standing-composition and source-coordinate
declarations; their mathematical statements and data are unchanged. The proof-term
change is recorded in
`coord/changes/T5-chart-source-coordinate-proof-instances.md`; the two external
consumers need no adaptation. The base-change component instance is recorded in
`coord/changes/T5-chart-base-change-proof-instance.md`; its four external consumers
also receive the definitionally identical map. The unit comparison now uses the
existing `smoothPurityUnitIso` wrapper with cached ordinary-unit endpoints; this
is the identical map by delta reduction, recorded in
`coord/changes/T5-chart-dualizing-unit-cached-endpoints.md`. Its seven external
consumers need no adaptation. The two rank-zero displays compose the natural
isomorphisms before evaluation, with the same maps by `NatIso.trans_app`; these
definitionally equal presentations are recorded in
`coord/changes/T5-chartAffineGamma_zero-natural-composition.md` and
`coord/changes/T5-chartStandardSection_zero-natural-composition.md`.

The unit-pullback definition checks its same three factors at an abstract ring
before specializing, as recorded in
`coord/changes/T5-chart-unit-pullback-generic-checking.md`. This changes no map.

## Proved and sorry left

Closed 18 of 26 original holes; added zero holes and split off zero statements.

- `chartOrdinaryOrientation_spec`.
- `chartCoordinateDifferences_neighbourhood`.
- `chartDiagonalNormalBundle`.
- `chartCoefficientUnit_finiteTor`.
- `chartProjectionUnitSource_existsUnique`.
- `chartGamma_counit_normalization`.
- `chartOrientation_coordinate_formula`.
- `chartNormal_model_exists`.
- `chartAffineMate_isIso`.
- `chartOrientation_coordinate_formula_forward`.
- `chartTraceProjection_smooth`.
- `chartStandardSection_formula`.
- `chartCoefficientUnit_constructible`.
- `chartDiagonalConormal_differentials`.
- `chartStandardSection_zero`.
- `chartCoordinateDifferentialFrame`.
- `chartNormalCoordinateMap_spec`.
- `chartCoordinateDifferences_over`.

The following original declarations remain `sorry`, all attached to
`lem-pur-diagonal-dnc-chart-normalization`:

- `diagonal_dnc_chart_normalization`.
- `chartOrientation_etale_restriction`.
- `chartOrientation_open_baseChange`.
- `chartGamma_eq_inverseOrientation`.
- `chartNormal_vectorPurity_normalization`.
- `chartEpsilon_standing_composition`.
- `chartAffineGamma_zero`.
- `chartDiagonalDelta_coordinate_identity`.

## No longer needed

No original imports are removed and no modules are withdrawn. The proof uses
the public differential-frame theorem, so the temporary `import all` of
`Sheaf.AlgebraicGeometry.EtaleCoordinateDifferentialBasis` and the temporary
`WeilConjectures.AlgebraicGeometry.Modules.DifferentialsSections` import were removed.
The temporary `WeilConjectures.AlgebraicGeometry.TangentBundle` import is also
removed: the differential-frame uniqueness proof obtains quasi-coherence from
the already available finite locally free rank theorem.
The remaining normalization proofs still need the
original node's higher-level compatibility dependencies; no pruning of those
unfinished arguments is claimed. The proved affine-mate and standard-section
formulas use the defining ordinary-coordinate normalization directly rather than
projection-purity agreement. The neighbourhood proof uses the existing centred
etale-chart geometry and a pullback universal property; its proof does not require
the cohomological chart-mate dependencies.

## Where the brief, the DAG or earlier work was wrong

Several original proof plans invoke substantially more theory than their actual
statements require. The orientation witness follows directly from its unique
existence specification. Invertibility of the affine mate and the coordinate
formula follow from that specification at the identity chart. The normal model
is constructed by relative Spec and its augmentation equations, rather than by
choosing an unspecified bundle isomorphism. The explicit differential frame uses
the established public differential-frame theorem and proves uniqueness with the
free-sheaf universal property. No statement is disputed.

The high-level chart-mate compatibility dependency imports this module through
`GeneralChartComparisons` and `ChartDncVectorFactors`; importing that entire
dependency back here would create a Lean import cycle. The closed proofs use
lower-level declarations without that cycle. The eight original coherence
obligations are retained; their future proofs need an interface below that cycle.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
