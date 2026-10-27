## What changed

Proved the complete original `AlgebraicGeometry.polynomial_log_chart_regularity`
conclusion from an independent polynomial-chart calculation and the existing
`smooth_geometric_stalk_algebra`, flat regularity, flat height, and regular-local
localization theorems. Every original binder and conclusion is unchanged.

The Lean combination constructs the affine-space isomorphism by actual polynomial
variable renaming, proves compatibility on the polynomial coordinates, lifts the
vanishing-coordinate set through `ULift`, and identifies the two coordinate ideals
and their cardinalities. It then obtains all stalk and quotient properties from the
smooth-stalk theorem. The quotient closed-fibre isomorphism is built using the
image of the maximal ideal, the commuting quotient-map square, and the double
quotient equivalence. Flat regularity gives the regular quotient; the two flat
height formulas and the base log-regular dimension equality give the final dimension
formula by addition, with no cancellation or hidden finiteness assumption. The
canonical ring and quotient equivalences transport log regularity in both directions.

The seven existing `PolynomialLogChart` definitions were moved without changing
their names, signatures or bodies into the new `PolynomialLogChartBasic` module,
publicly re-exported by the item. This prevents an import cycle when the independent
chart theorem uses those definitions. The change record is
`coord/changes/B3-polynomial-log-chart-construction-ownership.md`.

The only new unfinished theorem is `polynomial_log_chart_stalks`: the fs chart,
characteristic, characteristic-rank and boundary-ideal calculation. It has no base
log-regularity assumption and proves none of the flatness, regularity or Krull
dimension conclusions; it is a strict part of the original argument. Its docstring
and node give the product-unit-face calculation and both ideal inclusions, as well
as the group-completion rank argument.

Sources checked: ILO Expose VI 1.1--1.2 and 1.8--1.9, printed pp.69--71 (PDF
pp.75--77); Stacks algebra.tex, lemma-dimension-base-fibre-equals-total (00ON)
and lemma-flat-over-regular-with-regular-fibre (031E). The unit record
`sk-i-curve-zero` and the latest blueprint unit were read; this is below its route
and no unit statement or step is bypassed.

Validation: all three modules compiled remotely; the final main module compiled
cleanly in 9.0 seconds, below the 60-second limit. There are no changed existing
consumer modules.

## Proved and sorry left

Original module: one hole removed, in
`AlgebraicGeometry.polynomial_log_chart_regularity`
(node `lem-trf-polynomial-log-chart-regularity`); zero holes remain there.

One hole added, in
`AlgebraicGeometry.polynomial_log_chart_stalks`
(new node `lem-trf-polynomial-log-chart-stalks`, module
`Sheaf.AlgebraicGeometry.PolynomialLogChartStalks`). Its proof is exactly `by sorry`.
This is a decomposition of the original hole, not a net proof-count reduction:
one original hole closed and one strictly smaller hole added. The main theorem's
combination proof and all six private helpers are complete. The construction
module has zero holes. Existing dependencies retain their own proof status.

## No longer needed

Removed the direct `LogRegularCompletedChart` import: no completed local chart,
Cohen ring, power-series presentation or completion theorem is used. The canonical
strict-local ring comparison now comes directly from its definition module through
`PolynomialLogChartBasic`; the old comparison declaration and its name are retained.

Removed the direct `AssociatedLogUniversalStalks` import: `IsChart` already supplies
the chart-stalk pushout required for the polynomial calculation; the main algebra
argument has no use for existence of an associated log sheaf. The chart-face theorem
remains in the new chart node's plan, including its own associated-log dependencies.

Removed redundant direct imports of
`Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`,
`Sheaf.TraceFormula.SmoothGeometricStalkAlgebra`,
`Mathlib.Algebra.MvPolynomial.Basic`,
`Mathlib.RingTheory.Ideal.Quotient.Operations`,
`Mathlib.AlgebraicGeometry.AffineSpace`,
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and
`Mathlib.AlgebraicGeometry.Noetherian`; the construction module supplies the
statement-level interfaces, and only the proof inputs actually used are imported
privately in the theorem module.

The original direct dependency `pqf-lem-locnoeth-lft` is unnecessary for the main
Lean proof, which obtains polynomial Noetherianity directly from the affine-base
Noetherian ring. It remains a valid input to the independent chart-stalk plan.
The original direct dependencies `lem-trf-associated-log-universal-stalks` and
`lem-trf-chart-face-localization-logification` are replaced at the main theorem
by the independent chart node; the chart-face argument remains needed below it.
No existing module or node is withdrawn or asserted globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed mathematical hypothesis was found. The chart-face
theorem does not itself perform the product-unit-face, rank, structural-germ or
ideal calculation, so those operations cannot be obtained merely by applying its
signature. The new chart-stalk node records this genuine missing part instead of
repackaging log regularity. All the algebraic steps beyond it are now Lean proofs.

The regularity transfer theorem returns `IsRegularLocalRing`, whereas this item
requires `IsRegularRing`. The proof explicitly uses the existing
`lem-weil-pbc-regular-local-localization` theorem for this conversion. It is a
generic algebra tool; the existing maintainer-owned `tool_uses` list was preserved,
and the new use is recorded here for the independent reader's route check.

There are zero direct existing importers of the item, so the definition extraction
requires no forced adaptations. Exact source comparison confirms that the original
theorem signature is unchanged and all seven definition blocks differ only in their
blueprint ownership tags. New-statement edge cases checked: zero variables, empty
vanishing-coordinate set, the empty spectrum, all coordinates vanishing, and a base
chart with units. The rank formula is compatible with infinite rational dimension.

## New nodes

`def-trf-polynomial-log-chart-constructions` owns the seven existing concrete
polynomial-chart constructions in `PolynomialLogChartBasic`. It introduces no
new mathematical notion or unfinished data; it makes their definition ownership
independent of the regularity theorem. Its statement dependencies use the existing
log, polynomial, strict-local comparison and strict-henselization-map definitions.

`lem-trf-polynomial-log-chart-stalks` states only the fs, characteristic, rank and
nonunit-ideal calculation for a polynomial chart, with no log-regularity assumption.
Its four proof steps use finite product saturation, the unit-face localization
and chart logification theorems, rationalized group-completion ranks, and the two
explicit ideal inclusions. It is needed by and strictly smaller than the item.

Searches were run via `msearch.py` (LeanSearch, Loogle, LeanFinder and source grep),
with their actual records in the new nodes. No existing Mathlib or project theorem
states the chart calculation. The existing seven project constructions are moved,
not duplicated. A full blueprint search found no matching polynomial-chart or
characteristic-monoid blueprint node. Change record:
`coord/changes/B3-polynomial-log-chart-construction-ownership.md`.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
