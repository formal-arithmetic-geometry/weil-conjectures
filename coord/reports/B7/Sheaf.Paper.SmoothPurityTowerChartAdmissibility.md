## What changed

Replaced the single sorry in tower_chart_admissibility by a full Lean assembly:
finite origins are obtained from finiteRing_constructibleDerived_origin and the exact
Tor-interval comparison; scheme and coefficient facts use existing Noetherian/finite
instances; chart bounds use two successive inverse images, Tate tensor and shift;
ordered affine-stage bounds are proved by induction; open and geometric-point smoothness
use the existing relative-dimension instances; compact-support bounds and all output
domains are then applied separately to each map and compactification.

Moved the unchanged 13 data declarations to SmoothPurityTowerChartData and publicly
re-exported them from the item. The exact relocation and consumer analysis are in
coord/changes/B7-chart-data-dependency-direction.md. No downstream module is edited.
Added general tower-domain, elementary-operation and smooth compact-support interfaces,
each strictly smaller than the chart-admissibility conjunction, with sourced proof
plans. The compact-support interface is proved; only the other two contain sorry.
The existing definition-owner attachment follows the moved declarations.

## Proved and sorry left

Closed the original hole in
AlgebraicGeometry.ProEtale.SpChartAdmissibility.tower_chart_admissibility (one of one).
This is a decomposition, not a complete axiom-clean proof: the original top statement
is unchanged and its combining proof has no sorry. The finite_origins, tor_of_iso and
scheme_facts private helpers are proved. The new smooth_tower_compact_bounds theorem
and its open-coordinate and finite-property transport helpers are also proved, using
the existing compactSupport_uniform_tor_bound declaration.

Holes added and left (two):

- AlgebraicGeometry.ProEtale.SpChartAdmissibility.domain_of_level_bounds
  (lem-sp-level-bounds-tower-domain).
- AlgebraicGeometry.ProEtale.SpChartAdmissibility.elementary_tower_bounds
  (lem-sp-elementary-tower-bounds).

No sorry is inside a definition, private helper or partial combining proof. The
two remaining assertions concern individual domains or elementary operations; none
repackages the chart theorem, its recursive intermediates or geometric conclusions.

## No longer needed

The item's private proof imports removed are ExtensionIntegersDvr, RootTowerFiniteTensor,
ModulePullbackTensorIso, FiniteEtaleTwistLine, EtaleScalarFlatModel,
EtalePullbackLineFlatModel, EtaleInverseImageModulesExact, FlatConstructibleTensor,
SupportComparisonPullbackCoherence, ConstructibleComparisonFlatPullback,
ProEtaleConstantExact and EtaleSmoothZeroDimensionalFibres. The finite operation inputs
are recorded as proof dependencies of the new operation lemma, and the smooth geometry is already supplied
by Mathlib/source instances. All original public imports remain to preserve consumers.

The direct item proof no longer needs lem-weil-l-adic-extension-integers-dvr,
lem-weil-valued-dvr-finite-quotients, det-pe-finite-tor-comparison-noetherian,
lem-amb-root-tower-finite-tensor, lem-weil-pbc-ringed-topoi-module-pullback-tensor,
lem-asd-finite-etale-twist-line, lem-sp-etale-scalar-flat-model,
lem-sp-etale-pullback-line-flat-model, prop-weil-pbc-inverse-image-modules-exact,
lem-weil-pbc-exact-functor-complex-cohomology, lem-fd-flat-constructible-tensor,
lem-weil-pbc-comparison-pullback, lem-pe-constructible-comparison-flat-pullback,
prop-weil-pbc-proetale-constant-exact, det-sp-tower-shriek-levels,
lem-weil-pbc-open-immersion-etale,
lem-weil-pbc-etale-smooth-zero-dimensional-fibres,
lem-weil-pbc-qc-open-immersion-finite-type and det-sp-tower-bound-uniform.
Some remain necessary below the new bridge nodes or for unchanged data/public imports;
none is claimed globally withdrawn. Obsolete direct tool_uses approvals were removed
in their original order. No module is withdrawn or deleted, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The finiteTorComparisonNoetherian declaration uses the coefficient-model derived
presentation; it is not directly the intrinsic comparison in origins. The already
proved finite-ring origin theorem plus comparison_torAmplitudeIn_iff is a shorter
route to the exact required finite witness. The original plan's finite-ring coefficient
calculation is already embodied in spEllQuotientFinite/base.finite. The original chart
module also mixes data with its main theorem; separating the unchanged data is needed
to state independent bridge lemmas without a cycle.

The source route stays Local pairs and Uniformity of the current blueprint. Edge cases
checked: r=0 and d=0 give zero shifts; r+1 subtracts two from each endpoint; no input
normalization or compatibility of finite origins is assumed; empty schemes and zero
levels are allowed. The pullback/twist statements use Noetherian schemes rather than
a finite-field specialization. General helper statements have explicit source proof
plans and the three Mathlib searches plus project/blueprint duplicate searches.

## New nodes

lem-sp-level-bounds-tower-domain records only uniform membership, bounded-below actual
tower and independent origins from level bounds. Its source is chart proof steps 2--3.
lem-sp-elementary-tower-bounds records preservation by single inverse image, a specified
Tate tensor and an integer shift, from source steps 4--6. The main theorem supplies the
iteration and chart composition itself. lem-sp-smooth-tower-compact-bounds records only
finite output bounds for one map/compactification, proved from the existing uniform
compact-support theorem and the canonical open-adjunction coordinate comparison;
domains are supplied
by the separate domain lemma. All three use the same current Local pairs/Uniformity
source and carry the semantic, type-pattern and source search results.

Validation: remote single-file compilation passed for the combining proof and the
compact-support proof. The final full sandbox compile checks the relocated data and
all theorem modules together in import order; delivery runs the project preflight.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
