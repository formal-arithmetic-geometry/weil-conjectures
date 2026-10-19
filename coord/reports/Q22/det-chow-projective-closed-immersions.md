# det-chow-projective-closed-immersions — Q22

## Files written

- dag/nodes/sec-nagata-compactification/det-chow-projective-closed-immersions.json: existing statement, completed six-step split, no whole-item Mathlib match. Statement unchanged.
- citations.json: one verbatim statement quotation for every citation in the six proof steps.
- report.md and searches.jsonl: report and actual search log. No new DAG nodes and no new Mathlib leaves.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint id and the Chow/projective-space notions. Read AlgebraicGeometry/ChowLemma.lean:375 and AlgebraicGeometry/ChowLemma/EmbeddingOver.lean:125. The declarations AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpace and AlgebraicGeometry.ChowModification.isClosedImmersion_toProjectiveSpaceSource impose IsNoetherian S. They therefore do not prove this item over an arbitrary qcqs base. The generic ProjectiveSpace lift closedness result covers an ingredient only, not both properness/projectivity conclusions. The upstream master is reference material, not an attachment source.

## WANTED

None. All sources used are available locally.

## Corrections to the imported split

The imported proof already had the right graph route, but its first paragraph did not cite proper composition and its second paragraph cited no node at all and left elementary null. The projective conclusions did not explicitly verify the quasi-compactness in the library's projective convention. The replacement supplies existing nodes for those facts, identifies the graph by a direct specialization of the existing fibre-product change-of-base statement, checks the cartesian square for the second arrow, and writes out the projective-space identification preserving its projection. It creates no lemma restating either clause of the item. It adds the definition dependencies actually used in the statement.

The current blueprint node markdown contains the statement only. The detailed proof is in its imported DAG proof and in current unit sk-thm-chow-projective steps 1 and 2. The split follows those two steps; qcqs Chow existence belongs to det-chow-projective-qcqs-chow and the unit's third step, not this conditional lemma. The chapter route is unchanged. This item is not the unit's key statement sk-thm-chow-projective, so no unit realization fields are changed.

## Not duplicates

There are no new nodes to compare. Whole-DAG and whole-blueprint searches found lemma-weil-pbc-chow-embedding-over-x, which overlaps the second closedness assertion but does not state the whole item; it is not a same_as identification. Other existing generic facts are cited instead of recreated. In particular the graph is obtained by specializing lem-weil-pbc-fibre-product-change-of-base-closed-immersion with maps pi and id_X, and closed composition uses the first clause of lem-weil-pbc-closed-immersion-products.

## Mathlib searches

Ran and read LeanFinder twice with different formulations, Loogle with the expected notions and then with IsProper.of_comp, LeanSearch in plain words, and source grep through the prescribed msearch.py command. All exact queries are copied from searches.jsonl into mathlib_searches. Loogle's first query reports the unknown identifier AlgebraicGeometry.IsProjective; this is recorded as that result, not a claim that proper-to-separated is absent. Read Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:124 and Separated.lean:130–145. The hits supply individual ingredients already represented in the DAG; none gives every clause of the item by one specialization. No unexecuted search is recorded, and no service returned unavailable in these calls.

## Review by Q22

I read the current chapter and unit records, the current blueprint item's statement, and the imported proof. I checked Stacks morphisms.tex Tag 01W3 (lemma-composition-proper), Tag 01W6 (lemma-image-proper-scheme-closed, especially part (2) and its graph proof), Tag 01W8 (definition-projective), and schemes.tex Tag 01KR (lemma-fibre-product-after-map), Tag 01KS (lemma-semi-diagonal), Tag 01JY (lemma-base-change-immersion), and Tag 01IQ (lemma-immersion-when-closed). Tag 02V0/lemma-composition-immersion gives the composition clause. I checked the tags against the repository's tags/tags mapping. The finite projective-space model is the existing def-nagata-projective-space-base-change, whose homogeneous-coordinate convention distinguishes P(n;S) from classical P^n_S.

Step 1 uses precisely the composite assertion of lem-weil-pbc-proper-composition, the all-schemes finite-index assertion of lemma-nagata-projective-space-base-change-proper, and the separated clause of def-weil-proper-morphism. Its two input maps are proper hypotheses, not consequences of surjectivity. The projective-space lemma does not require a Noetherian base. Step 2 uses exactly the triangle assertion of lem-weil-pbc-proper-to-separated, with structural map a=f pi, target P^n_S and target structure map q_S, then the immersion-to-closed conclusion of lem-weil-pbc-proper-immersion-closed. The S-morphism equality is the assumed q_S i_S=f pi, so every hypothesis of these two nodes holds.

Step 3 reads the statement of lem-weil-pbc-fibre-product-change-of-base-closed-immersion, not its proof: instantiate its common intermediate target T with X and its two arrows with pi and id_X, and its separated arrow h with f. Proper implies separated by def-weil-proper-morphism. The resulting closed map has source tilde X times_X X; the inverse-to-first-projection formula identifies it with the graph using exactly def-pc-fibre-product's projections and uniqueness. Thus the cited node really supplies the required closed immersion. This uses the prescribed diagonal/graph route and does not import a different Chow theorem.

Step 4 uses precisely lem-weil-pbc-closed-immersion-base-change, with i=i_S (closed by step 2) and the map to its target the projection P^n_S times_S X to P^n_S. I wrote the universal-property argument verifying the source pullback and its projection, using def-pc-fibre-product. This is a statement about scheme morphisms, not just set-theoretic images; in particular it remains correct for nilpotent thickenings. Step 5 uses only the composition clause of lem-weil-pbc-closed-immersion-products, after steps 3 and 4 prove both factors closed. The projections of the composite are explicitly i_S and pi. The symmetry and reassociation are written by their maps on arbitrary test schemes, using def-pc-fibre-product and the actual absolute-base-change definition def-nagata-projective-space-base-change. The isomorphism preserves the projection to X, which is needed for the conclusion about pi.

Step 6 is elementary after the embeddings have been proved. It uses def-pc-projective-morphism for H-projectivity plus quasi-compactness, def-weil-proper-morphism for finite type of a and pi, and def-weil-finite-type-morphism for finite type implying quasi-compactness. It assumes no finiteness-presentation hypothesis. The convention is explicitly the blueprint's finite-projective-space convention, rather than silently substituting the broader Stacks projective-bundle convention.

I opened the complete statements of every cited node and generated citations.json by copying those statements verbatim. Each of the assertions used above occurs in the cited statement. There is no dependence on a definition node for an unstated theorem, and no missing stability assertion: proper composition, the proper triangle, immersion closedness, change of base, and closed composition are each carried by cited nodes. The only non-finished off-unit generic tool requiring a route declaration is lem-weil-pbc-closed-immersion-products; its composition clause is recorded in split_report.tool_uses. The other tools are Mathlib leaves or closed, and notions remain notions. None replaces a unit step.

Against delivery-errors B–E: no new unsplit nodes, proof-bearing new statements, invented notions, duplicate nodes, or relabelled clauses were introduced; the original statement and import metadata are preserved. Every step has an explicit elementary judgment and a local source, and proof_deps is exactly the union of uses. No non-elementary step exceeds 2000 characters (the longest is under 1100), and the inline identifications are direct fibre-product universal-property calculations, not hidden comparison lemmas. I checked that this proof uses no Noetherian, reducedness, finite-presentation, affine-base or flatness assumption. Empty sources, n=0, the identity modification, and nonreduced schemes cause no change to the arguments; all pullback and graph identifications are scheme-theoretic. Properness of f is essential to the graph step: its separatedness makes the diagonal argument available. The qcqs and surjectivity assumptions are retained even though the conditional closedness argument itself does not need them. No source error or statement dispute was found.

## Unfinished work

None in this one-level split. No Lean file was written or compiled. The cited imported generic projective-space properness node is reused as required and not resplit here; the unsplit Chow existence dependency remains a separate item.
