## What changed

Restored the quarantined module `Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion`
from its rework archive and retained its complete proof of
`AlgebraicGeometry.perfect_degreeZero_fibre_criterion`. The withdrawn
`Sheaf.AlgebraicGeometry.DerivedPullback` public import was replaced by the adopted
`WeilConjectures.AlgebraicGeometry.DerivedPullback` module, which provides the same
`derivedPullback` interface. No theorem statement or declaration visibility changed.

The proof uses the finite-free residue model, the rank-one residue stalk criterion,
localized homology comparisons, an explicit split of the connective complex, and the
bounded finite-free retract argument for perfection and positive tensor amplitude.

## Proved and sorry left

This is a rework restoration with no remaining holes. The item declaration
`AlgebraicGeometry.perfect_degreeZero_fibre_criterion` is proved; 0 of 0 item sorries
were closed, 0 sorries were added, and no split-off statements were created.

## No longer needed

The proof does not use the withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback` module;
its canonical adopted replacement is imported instead. No declared proof dependency or
DAG node is pruned: all dependencies used by the archived proof remain needed.

## Where the brief, the DAG or earlier work was wrong

The rework archive was complete, but its old public import referred to the withdrawn
Sheaf wrapper. With that wrapper absent from the current library, the import had to use
`WeilConjectures.AlgebraicGeometry.DerivedPullback` directly. The first compilation
confirmed that this replacement resolves `derivedPullback` and all dependent types.

Change record: `coord/changes/perfect-degree-zero-fibre-criterion-restore-C3.md`.
The only quarantined direct consumer is
`Sheaf.AlgebraicGeometry.SmoothCurveEtaleStructureDirectImages`; its interface and
planned invocation remain valid. The item node and unit route are unchanged.

Searches in this session: msearch LeanFinder returned general derived-category
bounds and local algebra results, without the sheaf-level fibre criterion;
Loogle returned no match (`IsIso` unknown to that service), and msearch grep found
no matching criterion. The existing library proof was therefore restored rather
than replaced. Single-file compilation completed without errors or warnings.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
