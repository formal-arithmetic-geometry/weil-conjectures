## What changed

Proved `AlgebraicGeometry.Scheme.integralPerfectChart_complete` without changing
its signature. The proof first proves intrinsic completeness of the completed
constant perfect model on the Noetherian base. It then applies the existing
stratum restriction theorem along the immersion preceded by the pro-etale chart.
Proved scalar and slice equivalences turn the supplied slice isomorphism into
an isomorphism of ordinary datum pullbacks. Cancelling its invertible prefix
proves the requested intrinsic unit is invertible for the supplied representative.

Added the proved theorem `cechPerfectModel_intrinsicComplete` in
`Sheaf.Paper.CechPerfectModelCompleteness`. It adapts the already proved
finite-projective model and sheafification comparisons to the precise
`AsSmall.{0}` site of intrinsic completion. The existing coefficient equivalence
and scalar-preserving Koszul transport identify the specified completion unit;
the existing constant-completion reflector criterion then applies. All helpers
are proved. No existing dependency or source-library module was edited.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.integralPerfectChart_complete`.
Added zero holes. All delivered modules contain zero `sorry` declarations.
The new public theorem `AlgebraicGeometry.Scheme.cechPerfectModel_intrinsicComplete`
is proved; it is not a split-off obligation. Existing imported theorem obligations
remain with their own modules.

Validation: all five delivered Lean modules compiled in dependency order through
`lcompile.py`, with per-file times from 22.3 to 34.1 seconds. The delivery tool
runs the independent preflight and axiom probes. No hypothesis was added to the
assigned theorem, and no target statement or definition was changed.

## No longer needed

The original two public imports are retained. No original import was removed.

The assigned node no longer needs a separate DVR or maximal-ideal argument
(`lem-weil-l-adic-extension-integers-dvr`): the datum supplies scalar-ring
Noetherianity and the degreewise finite-projective completeness calculation works
for every ideal. Its separate completed-realization cohomology dependency
(`lem-weil-pbc-completed-realization-derived-cohomology`) is also unnecessary:
exact termwise functors and their localization factorization isomorphisms give
all comparisons used here. These are changes to this proof route, not requests
to remove declarations from the adopted source library.

The constant-completion equivalence, intrinsic completion definitions and
finite-projective model calculation remain needed through the new proved module.
The stratum completion-unit restriction theorem remains a direct dependency.
The ordinary integral local-model theorem and extension-by-zero model transport
are not imported: their current import closures reach this item, so importing
them would create a cycle. The required independent slice/scalar constructions
are implemented as proved helpers of the separate chart comparison module instead. No unit-realized node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The completeness calculation and the intrinsic completion presentation use
`AsSmall` sites with different lift parameters. Their topologies cannot simply
be identified by definitional equality. The new proved module repeats the
site-dependent comparison on the exact intrinsic site while reusing the generic
scalar-extension, finite-retract and multiplication-difference proofs. The
final proof needs no compatibility of completed constant realization with
scheme pullback: completeness is transported from the base instead.

## New nodes

`lem-weil-pbc-cech-perfect-model-completeness`, attached to the proved theorem
`AlgebraicGeometry.Scheme.cechPerfectModel_intrinsicComplete` in the new module
`Sheaf.Paper.CechPerfectModelCompleteness`. It is the coefficient-model part of
the argument, with no immersion, slice isomorphism or target object hypothesis.

`lem-weil-pbc-cech-perfect-complex-model`, attached to the proved theorem
`AlgebraicGeometry.Scheme.CechPerfectModel.cech_model_complete` in
`Sheaf.Paper.CechPerfectComplexModel`. This is the termwise finite-projective
model calculation, separated to keep compilation within the per-file limit.

`lem-weil-pbc-integral-chart-pullback-comparison`, attached to the proved theorem
`AlgebraicGeometry.Scheme.integralLocalDerived_pullbackIso` in
`Sheaf.Paper.IntegralChartPullbackComparison`. It handles arbitrary complexes,
without completeness or perfectness assumptions. This separates the chart
normalization from the final theorem and its compilation cost.

`lem-weil-pbc-integral-pullback-scalar-comparison`, attached to the proved theorem
`AlgebraicGeometry.Scheme.proEtaleRingDerivedPullback_scalarComparison` in
`Sheaf.Paper.IntegralPullbackScalarComparison`. Its explicit private construction
is also used by the chart comparison. It is the generic adjunction normalization
step, separated after profiling to meet the per-file compile limit.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
