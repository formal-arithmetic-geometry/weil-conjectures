## What changed

Retired `Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension`, as
listed in `coord/retire-items.tsv`, using `deleted.txt`. Its stalk-dimension theorem
already exists, with the identical full signature and a complete proof, in
`WeilConjectures.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension`.
Reattached `lem-ag-rational-point-stalk-topological-local-dimension` there.

Its only current direct importer, the unclaimed
`Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`, uses only the general
open-embedding helper. Relocated that helper's existing complete proof into the
consumer as a private theorem and removed the obsolete proof import. Updated the
fibre-dimension node's description of this helper. All public declarations and
public imports of the consumer remain verbatim. No source-library file changes.

Change record:
`coord/changes/B3-retire-rational-point-stalk-topological-local-dimension.md`.
It lists all 55 transitive consumers and the effect on each.

## Proved and sorry left

This is a duplicate retirement with zero initial holes: proved 0 of 0 sorries;
0 added, 0 split off, 0 left. No decomposition.

`AlgebraicGeometry.ringKrullDim_stalk_rationalPoint_eq_topologicalKrullDimAt` is
retained at the existing source declaration, with unchanged statement and proof.
A direct compile importing it and printing its axioms reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The relocated private `localDim_openEmbedding` is fully proved. The adapted
`AlgebraicGeometry.fibre_dimension_after_base_change` compiles without errors or
warnings (1.9 seconds). There are no `sorry` declarations in the delivery.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.RationalPointStalkTopologicalLocalDimension` and its
sole remaining import from `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`.
The consumer needs no stalk-dimension comparison at all. The general topological
helper now lives privately in that consumer, its only caller.

The retired duplicate's imports of finite-type morphisms, ring Krull dimension,
closed-point localization dimension, and closed immersions no longer enter the
fibre-dimension proof via that duplicate. Its existing dimension-topology import
remains in the consumer. The source theorem still needs its own original imports
and the `lem-weil-pbc-closed-point-dimension-local-ring` dependency; those are not
pruned. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief does not describe this item's present state: it contains
zero holes and is explicitly a duplicate-retirement item. The stale node attachment
pointed to the Sheaf twin although the source library now proves the same theorem.
The older retirement inventory mentioned a second direct consumer,
`Sheaf.AlgebraicGeometry.RationalPointLocalDimensionBaseChange`, which has already
been retired; its surviving source counterpart imports the source theorem directly.

Earlier N3 work exposed the helper in this module for reuse. That was useful while
this module remained live; now its sole consumer must retain the proof locally so
the duplicate stalk theorem and its module can be retired completely.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
