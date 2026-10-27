## What changed

Replaced the sole hole in
`AlgebraicGeometry.affineGroupoid_exists_invariant_rank_strata` by the three-step
assembly already recorded in `lem-a1-affine-groupoid-invariant-rank-strata`.
The statement and both public imports are unchanged.

The proof applies `affine_split_morphism_positive_rank_pieces` to the source
and its identity section, converts the resulting finite set of nonempty positive
degrees into a `Finset`, and proves the covering clause pointwise using each
point's fibre degree. It obtains invariance from
`groupoid_source_pullback_translation`, then applies
`IsGroupoidScheme.existsUnique_invariantOpen_restriction_degree` on each piece.
Uniqueness identifies its restricted source with `morphismRestrict`, so the
known degree transfers to that source and then to the target. The comparison
map of pullbacks is `pullback.map`; its projection equations are proved by simp.
The nonempty and empty-object clauses are retained explicitly.

Added only private proof imports of the three recorded dependency modules:
`Sheaf.AlgebraicGeometry.AffineSplitMorphismPositiveRankPieces`,
`Sheaf.AlgebraicGeometry.GroupoidSourcePullbackTranslation`, and
`Sheaf.AlgebraicGeometry.GroupoidInvariantOpenRestrictionDegree`.
No other existing module, declaration, definition, node, or public interface changes.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.affineGroupoid_exists_invariant_rank_strata`
(node `lem-a1-affine-groupoid-invariant-rank-strata`).
Zero holes remain in the item; zero holes were added or split off.
This is a complete assembly proof from the three existing stated dependencies,
whose own proofs are not supplied by this delivery.

## No longer needed

Removed these redundant direct proof imports from the item:

- `WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`
- `Mathlib.AlgebraicGeometry.Morphisms.FlatRank`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`

All three current DAG proof dependencies are used. No DAG node or library module
is withdrawn or claimed to be globally pruned; the lower ingredients needed by
the three dependency lemmas remain their responsibility. The node's existing
three-step proof, proof dependencies, and origin already describe this proof,
so no node update is necessary.

## Where the brief, the DAG or earlier work was wrong

The item's docstring still expands the older seven-step mathematical plan;
the current DAG has already factored that argument into the three stated
lemmas used here. There is no mathematical discrepancy and no statement repair.
LeanFinder, Loogle, and grep searches found no shorter existing result.

Validation: `lcompile.py` compiled the finished module successfully with no
warnings in 5.7 seconds. Import-direction checks accepted all three proof imports.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
