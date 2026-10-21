## What changed

Restored `Sheaf.AlgebraicGeometry.RelativeMVResolvedRowRoofComparisons` from
the complete archive named in `coord/rework.tsv`. Preserved its public
theorem `AlgebraicGeometry.relativeMV_resolved_row_roof_comparisons`,
docstrings, imports, private constructions and mathematical proof route.

The proof uses Mathlib's surjectivity of localization into K-injective
complexes to obtain the two coefficient lifts. Naturality of the open
restriction units and restriction maps constructs the concrete row map.
The existing `relativeMV_resolved_roof_vertex_normalization` then supplies
the six vertex comparisons, three invertible denominators and three mate
equations. Its existential conclusion is passed directly into the two
outer roof witnesses, avoiding destruction and reconstruction of all
the dependent comparison witnesses. Kept the open adjunction and restriction
natural transformation folded when elaborating the private row map. Kept
right-derived functors and the ordinary direct-image functor folded during
the public theorem, and reduced its statement aliases without unfolding
row projections. The final implementation retains the archived private
row-map proof verbatim; no additional generic helpers are needed.

Change record:
`coord/changes/C2-relative-mv-resolved-row-roof-restoration.md`.
The theorem signature is textually identical to the archive; its sole
archived direct consumer is `RelativeMVDirectImageRowRoof`, which uses
the same arguments and conclusion. No consumer adaptation is required.

Validation: the complete final implementation compiled through `lcompile.py`
in 41.0 seconds, exit code 0, with no errors or warnings. The unchanged
archived direct consumer also compiled against the restored interface in
18.4 seconds. Its temporary test copy is not part of the delivery.
The unchanged single-file limit is 60 seconds. The unmodified archive
compiled in 55.5 seconds; intermediate elaboration experiments hit that
limit, motivating the local folding settings. No profiling or tracing
options remain in the delivered source. Every Lean line is at most
100 characters. Delivery preflight checks the actual module and its
axioms before pushing.

## Proved and sorry left

Assigned zero-hole restoration. Holes closed: none (0 of 0).
Holes added: none. Split off: none. Sorries left: none.
`AlgebraicGeometry.relativeMV_resolved_row_roof_comparisons`,
`resolution_map_surjective` and both commutativity proofs in `mv_row_map`
are fully proved. No theorem or data construction is left unproved by
this delivery.

## No longer needed

No imports, nodes or modules are pruned. Both public imports and the
private import of `RelativeMVResolvedRoofVertexNormalization` are retained.
The final proof no longer unpacks and repacks the twelve comparison
witnesses returned by that theorem.

## Where the brief, the DAG or earlier work was wrong

The operative assignment is the restoration in `coord/rework.tsv`,
following a failed cluster restore. The archived module already has
zero holes. It is not a missing or withdrawn mathematical statement.
The current claim names C2; `coord/returns/C2.md` has no item-specific
return.

Searching `dag/nodes` and `dag/units` by module, declaration and blueprint
identifier finds no attachment for
`lem-pc-relative-mv-resolved-row-roof-comparisons` in this snapshot.
The archived blueprint tag and dependencies are preserved; no substitute
node or proof obligation is invented. The mathematical route is unchanged.

All three required `msearch.py` searches ran. Loogle and grep confirm
`CochainComplex.IsKInjective.Qh_map_bijective`, which is already used;
LeanFinder returns general K-injectivity and injective-resolution lemmas.
Searches of both library roots find no shorter public replacement for
the specialized row comparison. The row construction uses functorial
naturality alone, so it requires no cover assumption and applies equally
to empty or repeated opens and zero complexes or coefficient maps.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
