## What changed

Filled `AlgebraicGeometry.Etale.AffineLineNormalizedDescent.sheaf_rigidity` in
`lean/Sheaf/AlgebraicGeometry/EtaleShiftedLineNormalizedDescent.lean`.
Affine-line fullness lifts the automorphism to an endomorphism of the base sheaf.
Naturality of the composite of `upperStarComp` and `upperStarId` identifies that
endomorphism with the identity after restriction to the unit section. Functoriality
then identifies the original automorphism with the identity. The proof does not use
local constancy, finiteness, or a nonzero coefficient ring. All existing signatures,
definitions, public imports, and docstrings are preserved.

## Proved and sorry left

Closed one of two original holes:
`AlgebraicGeometry.Etale.AffineLineNormalizedDescent.sheaf_rigidity`.
Added no holes; split off no statements.

One original hole remains:
`AlgebraicGeometry.Etale.AffineLineNormalizedDescent.normalized_descent`, node
`lem-trf-etale-shifted-line-normalized-descent`. Its existing source and complete
natural-language proof are retained verbatim. This is a partial proof delivery,
not a proof of the normalized-descent assertion.

## No longer needed

None. The existing imports and DAG dependencies remain needed by the retained
normalized-descent proof plan. No module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The first DAG step applies directly:
fullness suffices, with the unit-section natural isomorphism giving the needed
faithfulness on the lifted map. The source-library shifted-morphism descent APIs
also exist, but a covering-family adaptation was not completed. Experimental
private helpers were removed from the packet; no unfinished private proof or
additional statement is delivered.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
