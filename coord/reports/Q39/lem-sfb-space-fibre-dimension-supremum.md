# Q39: lem-sfb-space-fibre-dimension-supremum

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-fibre-dimension-supremum.json: split the unchanged statement into five steps.
- No new nodes: the initially proposed Descent 04N4 node was removed when the final refresh found Q11’s exact lem-sfb-etale-topological-dimension-at-point.
- citations.json: verbatim statement excerpts for every citation (the whole statement is retained where several clauses are used).

## Attachments

None. Searched the live project WeilConjectures tree for the exact blueprint tag, algebraic spaces, fibre dimension, local dimension and etale dimension. No project declaration supplies the algebraic-space statement. The scheme results in FibreDimension and NoetherNormalization do not state it. No Lean was written or compiled.

## WANTED

None.

## Findings and route

The statement is correct and unchanged. Stacks spaces-more-morphisms.tex Tag 0D4M (lemma-dimension-fibre), last paragraph, gives the scheme-target affine-atlas route. Read spaces-properties.tex Tags 04N5 and 04N6 and spaces-morphisms.tex Tag 04NM to distinguish chart dimension from the underlying topology and from dimension of a local ring. In particular the generic point of the affine line has neighbourhood dimension one but local-ring dimension zero. The proof never invokes the existing quasi-separated atlas/topological-dimension comparison, which would impose a missing hypothesis.

The unit and chapter records and the latest blueprint sk-thm-sf-ctf-stability-direct-images.proof.md were read. This is a foundational dimension input below paragraph (3), not a change of its direct-image route. The inherited created.item chain leaves the imported blueprint DAG: blueprint_refs.py ancestor returns None. The existing null ancestor and inherited via chain are preserved; the reused 04N4 node extends the chain and explains its precise supporting place. No unit realization field is due for this non-key input.

Mathlib searches were run only through msearch.py and read. For each of the item and new lemma, semantic queries, Loogle and grep were used, including a second phrasing. Hits were scheme etale/smooth classes, smooth relative dimension zero, scheme fibres, and unrelated order dimension lemmas. Mathlib/AlgebraicGeometry/Morphisms/Etale.lean lines 87–116 were read: they prove base-change instances and smooth relative dimension zero, not equality of neighbourhood dimensions. Searches and actual outcomes are preserved in searches.jsonl; the node records use the same tool and query strings. No leaf is claimed.

## Not duplicates

No new node is delivered. Initial whole-DAG searches found only the algebraically closed field case in lem-trf-etale-cover-field-curve-nodality, the nodal-family statement in lem-trf-nodal-family-etale-source-locality, and the different local-ring invariant in lem-sc-etale-local-dimension. After the first successful dry run, the final refresh exposed Q11’s concurrently landed lem-sfb-etale-topological-dimension-at-point, an exact statement of Descent 04N4. I opened it, verified its unrestricted hypothesis and neighbourhood-dimension convention, removed my proposed node, and changed steps 2 and 3 and their citations to that existing node. The searches remain preserved as research evidence; no duplicate is being delivered.

## Review by Q39

I read Stacks 0D4M's full proof, its chart definitions 04N5/04N6 and relative dimension convention 04NM, and Descent 04N4 (lemma-dimension-at-point-local), both statement and chain-lifting proof, for the reused 04N4 lemma. The latter explicitly uses the minimum of open-neighbourhood dimensions, and states the unrestricted etale invariance the common refinements need. Its statement has no proof, no hidden finite type or Noetherian assumptions, and no added conclusions.

For step 1 I opened each cited node. The atlas-refinement statement explicitly allows a quasi-compact algebraic space without separation and gives one affine atlas. The etale composition node includes open immersions and composition, as needed after restricting the scheme target to an affine open. Local finite type is the item's chart hypothesis. The affine fibre-product node applies because both U and the chosen target open V are affine; its tensor-product description makes P affine. The lft base-change node applies to any scheme base change, including Spec of the residue field. The affine-qcqs node supplies actual quasi-compactness of P. Since Spec of a field has just two opens, this makes its structure map quasi-compact, so the finite type definition applies. The space fibre-products node supplies representability and surjective etale base change. I do not infer the atlas map itself is quasi-compact.

Step 2 uses the compatible-point surjectivity formula of the point-open-calculus node twice, first on X_V and then on U times_X W. I checked the statement supplies precisely surjectivity to compatible point pairs, with no diagonal hypothesis. The scheme-fibre definition explicitly supplies the homeomorphism to the set-theoretic fibre, hence the unique lifted points. The representable-etale definition supplies the two scheme-test projections, and the existing Q11 04N4 node supplies equality of local topological dimensions under them. This proves chart independence in the item; it is not outsourced to a restatement of the desired conclusion.

Step 3 cites atlas base change for surjectivity onto an arbitrary affine fibre chart B, then 04N4 for its two etale projections and the existing supremum-of-local-dimensions node for dim B. P itself belongs to the chart family, so both inequalities are justified. No chart is assumed to descend to an etale chart of the original X, an inference that would be false in general.

Step 4 only reindexes the equal values already proved in step 2, using the topological supremum node's exact formula; thus the elementary flag refers to the assembly, not to an unproved geometric fact. Step 5 uses lem-kun-dimension-finite-type with P finite type over a field, precisely the hypotheses established in step 1. The remaining facts are elementary: a nonempty bounded subset of natural numbers has a maximum; a point has nonnegative neighbourhood dimension; an empty target admits only an empty source. The fibre/point nonemptiness equivalences were established by atlas surjectivity and step 2, not presumed for a map of topological spaces.

I checked B1–B10 (self-contained statement, exact Stacks tag/label, genuine logged searches, no proof on the reused 04N4 node, no upstream attachment), C1–C8 (opened every cited statement, no proof-only citation, no missing non-elementary fact, generic off-unit tools declared), D1–D5 (the item carries its common-refinement argument; the sole proposed lemma was replaced by the exact concurrently landed Q11 node), and E1–E7 (all hypotheses and fibre products checked). No statement correction was needed. Edge cases checked: empty X and an empty fibre of a nonempty X; identity maps; affine space and its generic points; a disjoint union of a line and a point; arbitrary residue fields including imperfect ones; nonseparated spaces (no separated atlas theorem is used). Each proof step is under 2000 characters; none hides a further standard identification. The common-chart construction and reindexing are written out.

## Unfinished work

Only the requested one-level split is delivered. No new node remains. There are no additional pending repairs.

Final delivery inventory: zero new nodes, zero new Mathlib leaves. The item statement remains unchanged.
