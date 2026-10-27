## What changed

Proved `AlgebraicGeometry.Scheme.fppfSheaf_coproduct_equality_locus` without changing its signature, definitions, or public imports. Added seven proved private helpers in the item module for coproduct geometry, extracting local equality data, lifting through open immersions over the base, sheaf separatedness, and restriction compatibility.

The proof follows the same-label partition argument. It handles the potentially larger index universe by showing the nonempty summands have a small index type, constructs global lifts by the existing partition theorem's scheme coproduct property, proves uniqueness using the disjoint labelled opens, and checks the pullback pointwise. Updated the existing node's proof and proof dependencies to this argument. No other module changed.

## Proved and sorry left

Closed the single original hole: `AlgebraicGeometry.Scheme.fppfSheaf_coproduct_equality_locus` (node `lem-trf-coproduct-equality-locus`). Original holes: 1; proved: 1; holes added: 0; split off: 0; remaining holes in this module: 0.

The proof uses the existing `AlgebraicGeometry.Scheme.fppfSheaf_coproduct_partition`, which remains unfinished in its own module and is not changed by this delivery. All added private helper proofs are complete. No data is chosen from an unfinished mere-existence theorem: selected points come from actual `Nonempty` witnesses; the selected lifts come from the supplied cartesian squares and their uniquely determined lifts.

## No longer needed

Removed the private import `Mathlib.AlgebraicGeometry.Gluing`. The direct proof dependency `lem-weil-pbc-scheme-morphism-gluing` is unnecessary: the already stated partition theorem supplies the stronger scheme coproduct universal property, so its colimit descent and extensionality assemble and compare the local maps. Removed this dependency from the node. It may remain needed transitively by the partition theorem; no global withdrawal is claimed. No modules or declarations are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically correct. The implementation needs an explicit size argument because I has universe max u v, while scheme coproduct geometry requires a u-small type. The private coproduct geometry helper proves smallness of the nonempty subfamily from its maps into disjoint opens of T, then reinstates empty initial summands. The unit route is preserved; this auxiliary node is not a separately realized unit step.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
