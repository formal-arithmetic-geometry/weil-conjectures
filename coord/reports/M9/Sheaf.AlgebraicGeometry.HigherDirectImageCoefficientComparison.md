## What changed

Completed the retirement assigned by `coord/retire-items.tsv` for
`Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientComparison`. Withdrew its
file through `deleted.txt` and repointed the Lean attachment of
`lem-pc-higher-direct-image-coefficient-comparison` to the existing theorem in
`WeilConjectures.AlgebraicGeometry.HigherDirectImageCoefficientComparison`.
The mathematical statement, proof dependencies and unit route are preserved.
Change record: `coord/changes/M9-retire-higher-direct-image-coefficient-comparison.md`.

The original copy compiled (25.0 seconds). A scratch theorem with its complete
original type was proved by applying the adopted source theorem (7.3 seconds).
Both that check and the source theorem have exactly the allowed axioms:
`propext`, `Classical.choice`, `Quot.sound`. The sole DAG parent's original source
file, `WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineCohomologyPresentation`,
also compiled unchanged (38.5 seconds). All checks used `lcompile.py`.

## Proved and sorry left

The assigned module already had zero holes. Closed: zero; added: zero; split
off: zero; remaining: zero. The existing complete proof of
`AlgebraicGeometry.higherDirectImage_coefficient_comparison` is retained in the
source twin and passes the original full type check. No new Lean declaration
or unproved intermediate result is delivered. This is a duplicate retirement,
not a new hole closure or decomposition.

## No longer needed

Retired module: `Sheaf.AlgebraicGeometry.HigherDirectImageCoefficientComparison`.
Its three imports leave with that duplicate:
`Sheaf.Paper.HigherDirectImagePresheaf`,
`WeilConjectures.AlgebraicGeometry.OpenRestrictionModuleCohomology`, and
`WeilConjectures.AlgebraicGeometry.HigherDirectImageResolutionNaturality`.
The source modules and both mathematical proof-dependency nodes remain needed
by the retained source proof; no other module or node is claimed pruned.

No live or quarantined Lean file imports the retired path. The only dependency
parent in the DAG is `lem-pc-higher-direct-image-affine-cohomology-presentation`;
it already attaches to the adopted source consumer and retains its dependency
on the same comparison node. No parent dependency is removed. All eight
retirement prerequisites in the queue have already been retired.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes proving a hole, but this item is explicitly
a retirement in the current retirement queue and has zero holes. Its historical
DIFFERENT classification comes from an explicit universe annotation in the
twin: the source theorem proves the original type without any adaptation.
The sole stale DAG attachment pointed to the duplicate rather than the adopted
source theorem. Its parent has already migrated; no consumer edits are needed.
No target statement, definition, upstream declaration, or unit route changes.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
