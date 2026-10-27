## What changed

Reduced `AlgebraicGeometry.ProEtale.SpPurityReduction.pullbackTower_bounds` to the
single-level preservation calculation
`AlgebraicGeometry.ProEtale.SpPurityReduction.pullback_level_bounds` in the new
module `Sheaf.Paper.PurityPullbackLevelBounds`. The new lemma applies to an
arbitrary derived strict tower, with bounded constructibility and finite Tor
amplitude assumed only at the specified level. It assumes neither tower
membership nor normalization and concludes only level constructibility and the
shifted Tor interval.

The item now proves the cohomological interval itself. Its proved private helper
`tor_cohomology` transports the intrinsic Tor predicate to fixed coefficient
sheaves, uses `DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn` (testing
against the tensor unit), and transports cohomology back along the exact
realization. The complete assembly unpacks the input tower's common Tor interval,
uses the local result at every level, proves the shifted interval inequalities,
and supplies all finite-level and common-interval fields of
`spConstructibleTorTowers`. It separately proves the claimed bounds for every
specified common input Tor interval. No existing signature or definition changes.

The new lemma's outstanding work is the finite quotient identification, pullback
and ordered-line tensor/shift transport. Its docstring and node give that argument
and its dependencies. The large exceptional-reduction theorem is unchanged in
this partial delivery. In particular no family of level morphisms is lifted to
a strict tower morphism and no reduction is inverted.

## Proved and sorry left

Original holes: 2. Original hole bodies closed: 1, in
`AlgebraicGeometry.ProEtale.SpPurityReduction.pullbackTower_bounds`
(node `lem-sp-purity-conjugates-tower-reduction`). This is a decomposition,
not a net proof: one strictly local preservation theorem is split off.

Original hole left:
`AlgebraicGeometry.ProEtale.SpPurityReduction.purity_conjugates_tower_reduction`
(node `lem-sp-purity-conjugates-tower-reduction`). Its statement, docstring,
and `by sorry` body remain unchanged.

Hole added:
`AlgebraicGeometry.ProEtale.SpPurityReduction.pullback_level_bounds`
(node `lem-sp-purity-pullback-level-bounds`). Its public proof is exactly
`by sorry`. The single-level statement covers dimension zero, the first
positive coefficient exponent, equal interval endpoints, and arbitrary
nonnormalized input towers. The uniform-category and cohomological conclusions
of the original theorem are absent from this lemma and are proved in the item.

There are two holes in the delivered Lean files in total, with net hole change
zero. `tor_cohomology` is fully proved and adds no hole. Both modules have been
checked through the required remote compiler; delivery performs the final packet
checks.

## No longer needed

Removed the item's direct private imports of
`Sheaf.Paper.PullbackTorAmplitude`, `Sheaf.Paper.TwistPreservesFiniteness`, and
`Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations`. The item's completed
assembly uses the new local lemma and
`Sheaf.AlgebraicGeometry.IntrinsicTorAmplitudeTransport` instead. Its old public
imports are all retained verbatim.

The direct Step 1 uses of `lem-sf-pullback-tor-amplitude`,
`prop-weil-twist-preserves`, and `def-sbc-smooth-morphisms` move to the new local
lemma's proof plan. They remain needed there; they are not globally pruned.
All remaining exceptional-conjugacy proof steps and their dependencies stay.
No module or declaration is withdrawn, and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken tool was found. The planned implication from the
Tor interval to the cohomological interval can be implemented using the existing
intrinsic-to-fixed Tor equivalence and the existing unit-test lemma. It needs no
additional open statement. The retained ordinary strict-tower data also lets the
remaining finite calculation be stated for an arbitrary tower with a one-level
hypothesis, rather than assuming the original uniform tower domain.

## New nodes

`lem-sp-purity-pullback-level-bounds`, module
`Sheaf.Paper.PurityPullbackLevelBounds`: one-level constructibility and translated
Tor bounds for the actual derived pullback tensored with the ordered shifted
Tate line. Source: latest tower-geometric gamma proof (3), finite-level part of
the item's Step 1. LeanSearch, LeanFinder, Mathlib grep and local source searches
found general pullback, twist, etale flat-model and tower-domain tools; none
states this single-level conclusion for the actual strict-system source. The
node records the quotient identification, finite pullback, line induction and
shift calculation. No change record is required: existing statements and
definitions are unchanged.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
