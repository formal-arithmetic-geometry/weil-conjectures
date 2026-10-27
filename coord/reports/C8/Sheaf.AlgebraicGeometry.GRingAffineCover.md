## What changed

Proved `AlgebraicGeometry.isGRing_of_affine_open_cover` in
`Sheaf.AlgebraicGeometry.GRingAffineCover`, preserving its signature and the existing
DAG proof route. Added the proof-only import `Mathlib.AlgebraicGeometry.Noetherian`.

The chart hypotheses give local Noetherianity by
`isLocallyNoetherian_of_affine_cover`, and hence Noetherianity of the arbitrary
affine section ring. For each prime q, its point x in V belongs to a chart U i.
The two affine stalk-localization equivalences identify the chart localization at
the prime corresponding to x with the localization at q. The maximal ideals agree
under this ring equivalence. `AdicCompletion.exists_ringEquiv` gives the compatible
completion equivalence, and `RingHom.IsRegular.of_ringEquiv` transports the chart's
regular completion map. This proves all defining conditions of `IsGRing`.

Validation: the assigned module compiled through `lcompile.py` in 7.3 seconds with
exit code 0 and no Lean diagnostics. The proof uses no finiteness, nonemptiness,
quasi-compactness or separation assumption. Empty schemes and empty affine opens
are covered: the prime-localization condition is vacuous when there are no primes.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.isGRing_of_affine_open_cover`
(node `lem-trf-g-ring-affine-cover`).

Holes added: none. Sorries remaining in the item: none. Split-off statements: none.

## No longer needed

None. All existing imports and all declared proof dependencies are used. The
Noetherianity, affine point/stalk comparison, completion compatibility, and regularity
transport steps all follow the existing DAG. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing plan is sufficient as stated.
LeanFinder returned generic affine-cover induction and morphism-locality results;
Loogle had no `IsGRing` match. Local source searches found no duplicate affine-cover
G-ring theorem. The direct stalk comparison implements the prescribed route without
needing finite basic-open descent or additional intermediate statements.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
