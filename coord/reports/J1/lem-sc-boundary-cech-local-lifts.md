# Delivery report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-boundary-cech-local-lifts.json` (item, repaired split).
- `dag/nodes/sec-curve-estimates/lem-sc-cech-h1-injective.json` (repaired statement-only input).
- `dag/nodes/sec-curve-estimates/lem-sc-boundary-cech-compatibility.json` (new statement-only general module input; no Mathlib match).
- `citations.json`.

2. Attachments: none.

3. WANTED: none.

4. Repair: I deleted `lem-sc-boundary-local-lift-rep`, because it restated the item's cocycle and boundary conclusion. The item now carries the cocycle argument itself. I added only the narrower general statement that, for a short exact sequence of O_X-modules and chosen local lifts, the Cech class of their differences maps to the connecting boundary. I also corrected the injectivity input to say explicitly that it is the canonical map for the underlying abelian sheaf, and added the canonical-map naturality and Cech-complex definition as statement dependencies and citations. Both created nodes have `created.by` and `created.date`.

## Review by J1

I read the item source in `/home/ubuntu/c1-stacks-review/cohomology.tex`, including Cohomology Lemma 0B8S (`cohomology-lemma-cech-h1`) for the local-lift boundary calculation and Lemma 0B8R (`cohomology-lemma-cech-h1`) for injectivity; the repository's imported labels are retained in the node source fields. I also read the existing `lem-sc-cech-h1-map-natural` statement and `def-weil-pbc-site-cech-complex` statement. The new compatibility node is stated for arbitrary short exact sequences of O_X-modules, rather than square-zero algebras, and its source is the 0B8S local-lift compatibility.

Step 1 uses only the Cech-complex definition: exactness of the displayed sheaf sequence puts each difference in I on the overlap, and the displayed three-term identity is a telescoping sum; the Cech definition supplies the degree-one cocycle relation. Step 2 cites the new compatibility node, whose statement explicitly gives `c_A([alpha]) = partial(s)` for the underlying module sequence. Step 3 cites `lem-sc-cech-h1-injective` for injectivity and `lem-sc-cech-h1-map-natural` to identify its `c_I` with the canonical map for the underlying abelian sheaf; the same argument is uniform for another section and local lifts. Every citation quote in `citations.json` is copied from the cited statement.

I checked the hypotheses at each use: X is a scheme, the cover is an open covering, the algebra sequence is short exact and hence an underlying module sequence, and the selected local lifts exist. I tested the one-open-cover and zero-kernel cases: the Cech 1-cocycle and boundary are both zero, and injectivity is consistent. The returned D1/D2, B3/C4, and B5 points are addressed by deleting the restatement node, citing the canonical-map and Cech-definition nodes in both relevant records, and explicitly using the underlying-abelian-sheaf interpretation.
