## What changed

Constructed the comparison family in
`WeilConjectures.commonStagePullback_comparison_data` explicitly by whiskering the
published rational pullback/scalar comparison with the recorded transition
identifications. Its hom and inverse components are the prescribed
`commonStagePullbackComparison`: equality of the isomorphisms follows from
the hom component by `Iso.ext`, and gives the inverse component as well. Added
`RationalPullbackStageCoherence` to prove
that the recorded stage tower equation follows from the coefficient-level square
in `RationalPullbackScalarTower`. The latter concerns three finite coefficient
fields and one rational object, before any algebraically closed coefficient
system or quotient category is formed.

The archived item was restored without deleting its declarations or changing its
signatures. The scalar-stage uniqueness specification identifies the chosen
system with the explicit transition/associator system; the coefficient-inclusion
composition law then removes the equality transports. The construction uses no
new coefficient objects or arbitrary isomorphisms. The category transport is proved
abstractly. The coefficient calculation compares whole natural transformations,
using the existing private normalized-associator API through `import all` of
`GeneralAlgebraicallyClosedCoefficientStages`, before taking components. This
resolves the otherwise expensive kernel conversion of coefficient witnesses.
No shared definition or attribute was changed. The extra reduction settings in
the item are local to the comparison and pullback descent proofs. A profiler
trace identified a costly conversion in the unchanged descent proof; keeping the
scalar category abstract and reducing its stage aliases avoids unfolding scalar
composition during that conversion.

Validation: `lcompile.py` accepted both new modules and the item. An initial
delivery compile then exceeded 60 seconds (61 seconds); nothing was pushed.
Profiling located the expensive category conversion, and the scoped reduction
settings were extended to the two pullback descent proofs for optimization.
The optimized item was accepted in 56.4 seconds; the last descent conversion
fell from about 5.9 seconds to 0.3 seconds in the profiler. All development
profiling options were removed. The delivery tool performs the final clean
compile and preflight.

## Proved and sorry left

Closed the textual hole in
`WeilConjectures.commonStagePullback_comparison_data`
(node `lem-weil-common-stage-pullback-comparison-data`) by a decomposition. The
component normalization and passage from coefficient associators to the recorded
stage-system associators are proved in Lean.

Added one hole:
`WeilConjectures.rationalPullbackScalarComparison_tower`
(node `lem-weil-rational-pullback-scalar-tower`). It is the coefficient-level
pullback square from the existing scalar-comparison argument, strictly before
common-stage construction. It asserts neither existence of a comparison family
nor existence of a quotient functor.

Retained the existing hole
`WeilConjectures.commonStageDerivedInternalHom_existsUnique`
(node `def-weil-derived-pullback-tensor-hom`).

Thus this is one decomposition of the two original holes, with one new hole;
there remain two textual holes across the delivered modules, for net zero holes
closed. The proved
`WeilConjectures.rationalPullbackStageComparison_coherent` uses the new
coefficient-level square.

## No longer needed

No import is removed. The existing `import all` accesses for
`BilinearCoefficientDescent` and `Mathlib.Logic.Small.Defs` are retained:
the earlier C4 report records that the generic family accessor bodies and the
small coefficient implementation are needed to identify the tensor interfaces.

The comparison-data node no longer invokes generic coefficient-pair descent:
that constructor belongs to the already proved
`commonStagePullback_descent_from_data`, downstream of comparison coherence.
The node now cites the normalized stage-coherence theorem instead. Generic
pair descent remains needed by the item, so no existing module is withdrawn or
claimed globally pruned. All public re-exports and all existing tensor and Hom
dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

At session start the item's live path was absent and `coord/rework.tsv` pointed
to its quarantine archive. The archive was used, preserving both original holes
and the existing declarations. During work the identical file reappeared in the
shared source tree.

The original comparison-data proof plan cited generic quotient descent as its
only dependency, but that theorem assumes the very comparison coherence needed
here. The missing argument is the coefficient-level tower square, not descent.
The new nodes separate this coefficient calculation from the proved stage-system
normalization.

Related rational tower statements in `RationalRestrictionComparisonCoherence`
and `IsomorphismPullbackTowerLaws` import this item, so they cannot be proof
dependencies here. They also specialize the geometric setting or require an
isomorphism. The local category-instance reduction follows the existing pattern
in `CommonStageTensorRightUnitorNaturality` and `CommonStageOpenHeartAdjunction`.

The latest blueprint now describes ambient condensed-coefficient operations in
`sec-proetale-coefficients/sk-prop-sf-open-closed-triangle`, while the assigned
node and existing Lean statements retain their earlier integral/rational and
common-stage interfaces. No statement was changed to resolve that discrepancy.

## New nodes

`lem-weil-rational-pullback-scalar-tower`: the normalized rational pullback square
for a tower of three finite coefficient fields. Its docstring and node specify
the ordinary comparison, completion conjugation, restriction and rationalization
argument, and check repeated fields, identity maps, zero objects and empty
schemes.

`lem-weil-rational-pullback-stage-coherence`: the proved passage from that square
to `pairFunctorCoherent` for the recorded coefficient systems, retaining both
stage associators. Both new nodes belong to the assigned chapter and unit.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
