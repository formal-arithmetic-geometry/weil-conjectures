## What changed

Withdrew the unimported duplicate
`Sheaf.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverseAux` using `deleted.txt`.
The adopted source module of the same suffix already proves the ring bridge and auxiliary
with identical signatures. Their DAG records now point to those upstream declarations.
The auxiliary proof record follows the upstream direct projection, bypassing the obsolete
locality wrapper; the wrapper node remains, with its Lean attachment set to null.
No source-library module or target statement is edited.

Change record: `coord/changes/polynomial-chart-stalk-flat-comparison-retire-twin.md`.

## Proved and sorry left

Original item: zero `sorry`s. Holes closed: 0. Holes added: 0. No split-off results.
No `sorry` is left in this delivery. This is a duplicate retirement, not a new proof.

The retained upstream declarations are
`AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_ring_bridge` and
`AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_aux`.
Their `#print axioms`, and that of the parent
`AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse`, report exactly
`propext`, `Classical.choice`, and `Quot.sound`. The original Sheaf item compiled in 3.3 s;
the joint upstream-import/axiom probe compiled in 2.1 s through `lcompile.py`.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.PolynomialChartStalkFlatComparisonReverseAux`.
Its unique local wrapper
`AlgebraicGeometry.polynomial_chart_stalk_flat_comparison_reverse_local_criterion`, node
`lem-sbc-polynomial-chart-stalk-flat-comparison-reverse-aux-bridge`, is no longer needed.
The adopted upstream auxiliary projects directly from the ring bridge instead.

All imports of the withdrawn Sheaf file disappear with it:
`WeilConjectures.AlgebraicGeometry.PolynomialChartFibreStalk`,
`Mathlib.AlgebraicGeometry.Morphisms.Flat`,
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
`WeilConjectures.AlgebraicGeometry.FinitePresentationStalkLocalizationModel`,
`WeilConjectures.AlgebraicGeometry.PolynomialChartClosedFiberModuleFlat`, and
`WeilConjectures.RingTheory.FlatOfFlatClosedFiber`.
These dependencies remain needed by the retained source proof; none is claimed pruned.
The ring-bridge and auxiliary nodes remain needed and attached to the adopted source.
No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The assignment predates the synchronized proof: the current item already has zero holes,
and its former parent now imports the adopted source copy. The DAG still attached the
ring bridge and auxiliary to the unused Sheaf duplicate, and retained a redundant locality
wrapper on the auxiliary's proof route. This delivery corrects those stale attachments.
LeanFinder and Loogle searches found general flatness/localization tools; the exact result
is already present in the adopted source library, so no further flatness theory is needed.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
