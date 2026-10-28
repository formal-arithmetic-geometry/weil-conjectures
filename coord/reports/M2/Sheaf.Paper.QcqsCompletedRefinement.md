## What changed

Filled `WeilConjectures.sfQcqsCompletedRefinement_exists` in
`Sheaf.Paper.QcqsCompletedRefinement`, preserving its full signature and its public import.
Added private proof imports and the proved private helper `finite_refinement_isIso`.
Updated the owning node `lem-zl-qcqs-completed-refinement` to record this proof route.
Also replaced the excessive public import of `WeilCompactSupportCohomology` in the
unclaimed `FrobeniusWitnessedCompactification` module with its actual lower dependency,
`WeilIndSheafCategory`. The former caused an import cycle when this proof imported the
finite-coordinate theorem. No declaration, definition body, attribute or instance in
that module was changed. See `coord/changes/M2-qcqs-refinement-import-cycle.md` for the
consumer review.

The finite helper retains an etale origin using `finiteRing_constructibleDerived_origin`,
then identifies the normalized finite isomorphism with `refinementOpenMap` by its
adjunction transpose. For the completed map, use `refinementOpenMap_scalar` and finite
scalar comparison on the auxiliary compactification of `d.i` with open `c.i` and proper
map `r.hom`. This proves all reductions invertible. Qcqs open completeness and the
realization for that auxiliary compactification give the hypotheses of the existing
complete constructible cone argument. Finally push the inverse open map along `d.g`
and insert inverse proper composition. The transpose equation is the existing
`refinementOpenMap_normalization`; the prescribed formula for rho holds by reflexivity.

The repaired `FrobeniusWitnessedCompactification` and this proof compiled without
warnings in 21.8 and 6.8 seconds. All three direct consumers then compiled unchanged
against the repair: `FiniteRingRefinementCoordinatesCore` (5.5 s),
`FrobeniusSquareExchange` (41.5 s), and `FiniteRingRefinementCoordinates` (4.5 s).
Their unchanged temporary source copies were removed. Delivery performs its final
compilation and axiom checks.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.sfQcqsCompletedRefinement_exists`
(node `lem-zl-qcqs-completed-refinement`).
The private helper `finite_refinement_isIso` is also fully proved.
Holes closed: 1. Holes added: 0. Remaining holes in this module: 0.
No split-off theorem or new module is added. Existing imported theorem obligations
remain the responsibility of their existing nodes.

## No longer needed

The item's original sole public import supplies its statement and is retained. Every
added proof import is used. In `FrobeniusWitnessedCompactification`, the high-level public
import `WeilCompactSupportCohomology` is replaced with `WeilIndSheafCategory`, which supplies
`zlFiberMap`. No other declarations from the high-level module are used there. This
removes that import edge, not the imported module or any of its declarations.

The owning node no longer directly uses
`lem-cbc-strict-tower-proper-open-calculus`
(`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`): the already stated scalar
compatibility square and normalized finite coordinate theorem provide the needed
proper/open comparison without a new strict-tower realization proof here.

It also no longer directly uses
`lem-sf-derived-complete-finite-reduction-detection`
(`Sheaf.Paper.DerivedCompleteFiniteReductionDetection`): that theorem detects equality
of maps under a finite shifted-Hom hypothesis. This argument needs only invertibility,
which follows from the existing complete constructible cone argument in
`Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence`.
These are removals from this node's proof dependencies, not module withdrawals;
other consumers and transitive imports remain relevant.
All other original proof dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The theorem is unchanged and no statement defect was found. The earlier plan did not
use the existing general-field finite-origin theorem, scalar-refinement square, and
qcqs finite-mate result together. They already suffice for this obligation, so a third
split is unnecessary. The finite-field-only normalized integral refinement theorem
cannot be used here: its current proof imports this item. The proof instead uses the
finite-coordinate theorem, after removing its excessive high-level Frobenius import.
The cycle discovered by delivery was
`QcqsCompletedRefinement -> FiniteRingRefinementCoordinatesCore ->
FrobeniusWitnessedCompactification -> WeilCompactSupportCohomology ->
FieldShriekCompositionQcqs -> FieldShriekCompositionIntegralComponent ->
QcqsCompletedRefinement`. `WeilIndSheafCategory` has no import route back to the item.

The auxiliary compactification is of `d.i`, and its target carries the structure
inherited from `d`; all needed instances are inferred or obtained from quasi-compactness
of `f`. No absolute separatedness, finite-field, algebraic-closure, nonempty-scheme,
or finite shifted-Hom hypothesis was introduced. No data definition contains a hole
or chooses an arbitrary witness from an unproved mere-existence theorem.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 5 OK.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.Paper.FrobeniusWitnessedCompactification": "8b4ff518f7e7437d42d31453da2d88792c735346", "Sheaf.Paper.QcqsCompletedRefinement": "86dee50d9a5d152bfa0ef9d48d38e5cc859b98c5"}, "results": {"Sheaf.Paper.FieldShriekCompositionIntegralComponent": {"hash": "1cf7d95c816de8c22ce7868d4d3133d33a1261c5", "status": "OK"}, "Sheaf.Paper.FiniteRingRefinementCoordinates": {"hash": "bfd2cca5df6e56576d8d9a091b9207ca491852e3", "status": "OK"}, "Sheaf.Paper.FiniteRingRefinementCoordinatesCore": {"hash": "d242c55dbbb2108655615fb131147ff96ba8c533", "status": "OK"}, "Sheaf.Paper.FrobeniusSquareExchange": {"hash": "7ebce78f7f19e0d89781a23e101d1e0957274850", "status": "OK"}, "Sheaf.Paper.RingOpenMapNormalizedRefinementIntegral": {"hash": "594abb17ca081c5b19e7b2e4709023405b7abfb2", "status": "OK"}}, "seconds": 59, "time": "2026-10-28T09:27:51+0800", "transitive": 0, "version": 1}
```

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
