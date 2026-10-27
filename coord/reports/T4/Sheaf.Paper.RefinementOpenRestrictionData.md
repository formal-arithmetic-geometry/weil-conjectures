## What changed

Proved `WeilConjectures.PurCompactSupport.refinementRestriction_data` directly in
`Sheaf.Paper.RefinementOpenRestrictionData`, keeping its statement and imports unchanged.
The private construction `counitRestriction` proves the general naturality calculation
from the naturality of two transformations, functoriality, and associativity.
The proved private helper `exists_counitRestriction_of_eq` whisks this construction
by an arbitrary functor and identifies its components with a specified family.
The public theorem specializes this helper using `refinementRestriction.eq_def`.
Before specialization it opens the compactification/refinement records and substitutes
the open-triangle equality; this prevents kernel conversion from expanding the
transported pullback isomorphism. No shared definition or attribute is changed.
Updated the item's DAG proof and dependencies to this categorical calculation.
The final item compiled through lcompile.py in 3.3 seconds with all debug options removed.

## Proved and sorry left

Closed the sole hole, `WeilConjectures.PurCompactSupport.refinementRestriction_data`
(node `lem-sf-refinement-open-restriction-data`). Holes closed: 1 of 1.
Holes added: 0. Split off: 0. No sorry remains in the delivered module.
Imported definitions and their existing proof dependencies remain as before; this
is not a claim that their entire import closure is already free of sorry.

## No longer needed

No Lean import was removed: the single public import provides the statement's definitions.
The proof uses the existing construction node
`def-sf-integral-refinement-normalization-data` via the defining equation of
`refinementRestriction`. Coefficient data and compactifications remain statement dependencies.
The following planned dependencies are unnecessary for this component construction:

- `lem-sfb-proetale-open-restriction-counit`
  (`Sheaf.AlgebraicGeometry.ProEtaleOpenRestrictionCounit`).
- `lem-sf-proetale-open-pullback-preserves-kinjective`
  (`Sheaf.AlgebraicGeometry.ProEtaleOpenPullbackKInjective`).
- `lem-sfb-proetale-identified-open-closed`
  (`Sheaf.AlgebraicGeometry.ProEtaleIdentifiedOpenClosed`).
- `lem-weil-pbc-proetale-ringed-open-closed`
  (`Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`).
- `lem-weil-pbc-proetale-derived-pullback-composition`
  (`Sheaf.Paper.IntegralFinitePullbackComposition`).
- `lem-pur-exact-adjunction-unit-shift-descent`
  (`Sheaf.CategoryTheory.ExactDerivedAdjunctionUnitShift`).
- `lem-sp-canonical-right-derived-adjunction-shift`
  (`Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`).
- `lem-weil-pbc-commshift-nattrans-comp-whisker` (Mathlib shift-compatibility leaf).

The existing `refinementPull` is already a natural isomorphism, and the specified
adjunction counit is already natural. Thus neither geometric invertibility calculations
nor shift compatibility are needed here. These are local dependency removals;
no module is withdrawn, and no assertion of global unreachability is made.

## Where the brief, the DAG or earlier work was wrong

The DAG overstates the dependencies of the data-only obligation: naturality of the
defining composite suffices. The geometric and shift dependencies concern the separate
invertibility and shift obligations. The unit's compatibility route is unchanged.
Searches through LeanFinder, Loogle and Mathlib grep were recorded using msearch.py;
Loogle found `CategoryTheory.Adjunction.counit_naturality`. Project search found the
analogous fixed-coefficient naturality proof in `ProperOpenCoefficientRefinement`.
No definition repair, statement correction, new node or consumer adaptation is needed.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.RefinementOpenRestrictionData": "de2fb28cb23976504cf08e53bb077eca3bb88408"}, "results": {"Sheaf.Paper.RefinementOpenRestriction": {"hash": "380a131577b6b214adc0dfa01534fd7a2fabe52c", "status": "OK"}, "Sheaf.Paper.RefinementOpenRestrictionIsIso": {"hash": "ad8cec52399e24eb6b0da6a1f9f2faf434638618", "status": "OK"}, "Sheaf.Paper.RefinementOpenRestrictionShift": {"hash": "a3546541af8806a2568d0c4615c254fb54f99571", "status": "OK"}}, "seconds": 20, "time": "2026-10-28T04:42:46+0800", "transitive": 0, "version": 1}
```

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
