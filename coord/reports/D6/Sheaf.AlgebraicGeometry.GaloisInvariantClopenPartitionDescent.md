## What changed

Proved `AlgebraicGeometry.existsUnique_clopen_partition_of_galois_invariant` in
`Sheaf.AlgebraicGeometry.GaloisInvariantClopenPartitionDescent`, preserving its full
statement and public imports. The proof follows all four existing DAG steps:
Mathlib supplies surjectivity of the scalar-extension projection; the existing
`AlgebraicGeometry.exists_closed_subset_of_galois_invariant` descends each closed
member; surjectivity transfers disjointness and covering; complementarity gives
openness; images of witnesses give nonemptiness; injectivity of inverse image
gives uniqueness of the ordered pair. No route, node or interface changed.

Validated the delivered module with `lcompile.py`: clean compile, 4.0 seconds.
Searches through `msearch.py` (Lean Finder, Loogle and grep) found no shorter
scheme-descent theorem; Loogle identified `Function.Surjective.preimage_injective`,
which is used for covering and uniqueness.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.existsUnique_clopen_partition_of_galois_invariant`
(node `lem-trf-galois-invariant-clopen-partition-descent`).

Proved 1 of 1 original sorries. Zero sorries remain in the item. Zero holes added;
zero statements split off. The proof uses the existing closed-subset descent
statement without altering its module or any other existing module.

## No longer needed

Removed the redundant proof import
`Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`; the retained
`Mathlib.AlgebraicGeometry.PullbackCarrier` and existing public imports supply
its underlying-map API. This removes no mathematical dependency: all three DAG
proof dependencies remain used. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing plan applies unchanged, including to infinite Galois
extensions and arbitrary schemes. No finiteness, connectedness or
quasi-compactness hypotheses were added. For an empty base scheme the original
nonemptiness hypotheses are impossible; the proof requires no extra case or
assumption. All nonempty witnesses used in the proof are existential witnesses
inside a theorem proof, not data definitions chosen from unproved existence.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
