# Stage-1 report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ordered-composition-complex-homology.json`: item, split in six steps; no exact project or Mathlib attachment found.
- `dag/nodes/sec-six-functors-basics/lem-sfb-linear-dual-dimension-rank.json`: statement, Mathlib leaf. Its finite-dimensionality and dimension clauses use `Subspace.instModuleDualFiniteDimensional` and `Subspace.dual_finrank_eq`; its rank clause uses `LinearMap.finrank_range_dualMap_eq_finrank_range`.
- `citations.json`: seven verbatim statement quotations for all seven step/node incidences.
- Sandbox support: `searches.jsonl`, `write_split.py`, and `edge_cases.py`; no Lean, repository, launcher, chapter, or unit files changed.

## Attachments

None. Searches in `lean/WeilConjectures/` by the blueprint tag, ordered/vector composition, proper interval, and dual-rank names found no declaration stating this item. Uses of the dual-dimension theorem in unrelated project proofs do not state the item.

## Wanted literature

WANTED: a published reference for the ordered-vector-composition / augmented-proper-product-interval chain comparison, for `lem-sfb-ordered-composition-complex-homology`. The source itself already described this as agent-formulated. The argument is supplied explicitly and marked `proof_origin.by = agent`; the requested reference does not block the split.

## Errors and changes

The statement is correct and unchanged. The original node had no proof. Its motivating blueprint path names an older snapshot. I read the corresponding file under `literature/blueprint/latest/`, current commit `7284bb09daf97437d544c51882b325f9c52cd345` from COMMITS.txt. Paragraph (3) now only gives the open/direct-image route; it does not prove the combinatorial calculation. The proof therefore honestly describes itself as agent-written algebraic detail under that paragraph. The chapter and unit routes are untouched. The ancestor command returns `None`, consistently with the inherited null ancestry and the already-reviewed proper-interval sibling; this was not replaced with an invented blueprint ancestor.

The zero multidegree is separated before applying the interval theorem, whose hypotheses require nonzero m and r at least one. The comparison includes the augmentation: a two-block tuple has coefficient -1, so the cumulative-sum map reverses the boundary sign; multiplying degree n by (-1)^n corrects it. Chain complexes are reindexed by C^j=C_{-j} before applying the cochain derived-category localization.

## Unfinished work

Nothing remains in the split. Only the two node JSON files and the report are delivery material; the new node is a Mathlib leaf with no proof or proof dependencies. There are no new unsplit obligations.

## Not duplicates

lem-sfb-linear-dual-dimension-rank vs lem-pod-cohomology-of-dual-over-field: the existing node is a theorem about derived duals of complexes over the fixed Poincare coefficient field E, perfect pairings and biduality; the new leaf is linear algebra for an arbitrary field and a single linear map, asserting dual term dimensions and image ranks. It does not duplicate a complex-duality clause.

lem-sfb-linear-dual-dimension-rank vs lem-weil-pbc-idempotent-charpoly-rank-nullity: rank-nullity concerns the kernel and image of one map; it does not compare the map with its dual or give dual dimensions. The item cites both inputs.

lem-sfb-linear-dual-dimension-rank vs lem-trf-vector-space-quotient-dimension: quotient dimension is reused independently and does not assert either dual identity.

lem-sfb-linear-dual-dimension-rank vs lem-sfb-finite-free-dual-chain-comparison: the latter is a signed internal module-sheaf tensor/Hom comparison on a scheme with condensed coefficients and native evaluation normalization, not dimensions and ranks of ordinary linear duals.

No other node uses the new leaf's Mathlib rank declaration. Whole-DAG keyword/title/declaration searches and blueprint_refs searches for ordered compositions, proper intervals, dual homology, cohomology of the dual, rank of the dual, transpose rank, and finite dimensional dual were read. The same-as lists are empty. The existing reviewed `lem-sfb-product-chain-proper-interval-homology` is reused rather than duplicated.

## Review by Q121

I read the latest direct-images blueprint proof, the chapter and unit records, the entire statement of each dependency, and the relevant Mathlib source. For the existing interval theorem I read its full statement and its reviewed proof: it gives augmented strict-chain homology, including degree -1, not merely an unaugmented topological analogue. For the new leaf I read `Mathlib/LinearAlgebra/Dual/Lemmas.lean` around lines 507–517 and 920–926: both V and W meet the field and finite-dimensional hypotheses, dualMap is precomposition, the finite-dimensionality instance supplies both duals, and the two named theorems give exactly every numeric clause. All Mathlib searches were executed through msearch.py and their log records were copied verbatim into the node records with honest match/no-match verdicts. A second phrasing was used for the item and for the dual input. No service was recorded as absent when unavailable.

Step 1 uses only the concrete tuple definition: every block has positive total weight, and bounded coordinate arrays are finite. I checked m=0 and r=0 directly; no nonzero block can sum to zero. Step 2 gives an actual inverse, using coordinatewise differences of a strict chain; each difference is nonzero, the endpoints are proper, and sums telescope. It treats n=1 as the empty chain and n<=0 as zero spaces, so no interval degrees are missing.

Step 3 uses the chain-complex definition from `def-weil-pbc-module-chain-complex-homology`. I checked its statement really defines a morphism by commuting differentials. Double-deletion cancellation proves d squared is zero, and the displayed coefficient comparison proves the minus sign. I checked n=2 and n=1 separately. This is an explicit basis calculation, not a hidden comparison lemma or an appeal to a source's omitted details. Step 4 uses only the localization functor in `def-weil-abstract-derived-category`; I also read Stacks Tag 05RU, derived-definition-unbounded-derived-category, in derived.tex. A functor sends two inverse morphisms to inverse morphisms, so no preservation theorem is missing.

Step 5 uses the homology functoriality stated by the chain-complex definition and the exact two clauses of `lem-sfb-product-chain-proper-interval-homology`. Nonzero m implies r>=1; in the Boolean case the support cardinal is the coordinate sum. Thus the shift is n-2 and the surviving degree is n=s, including s=1 and an empty proper interval. This is the only non-elementary combinatorial input, and it is already reviewed.

Step 6 uses the existing rank-nullity leaf and quotient-dimension leaf, whose statements I opened; I read the named Mathlib declarations in FiniteDimensional/Lemmas.lean and Dimension/RankNullity.lean. The image of the previous differential lies in the kernel because step 3 proves the composite zero. Its dimension as a subspace of cycles is its ordinary image dimension, since the inclusion is the identity on those vectors. The new leaf gives exactly the dual term dimensions and reversed incoming/outgoing ranks. Adding the two ranks to either homology dimension gives c_n, so cancellation proves the equality without an uncited universal-coefficient or exact-dual theorem. I checked n=0 with b_0=0. These are elementary arithmetic substitutions of cited statements, not a new lemma replacing an item clause.

I checked delivery-errors B through E against the actual files: the new node is self-contained, TeX uses single mathematical backslashes, it carries definitions for field/finite-dimensionality/dimension, it has no proof, all search results and source lines are real, and no new node restates the item. Every cited theorem says what the step takes from it, and citations.json checks its quotations as literal substrings. Proof-dependency lists are exactly the union of step uses. The only off-unit inputs are existing Mathlib leaves/definitions, which are permitted tools; the combinatorial input is in the item's unit. All six steps are below 1000 characters, hence none hides a lemma in a step over 2000 characters. No SGA source or alternate global route is used.

As an independent small-case check I ran `edge_cases.py` with exact rational Gaussian elimination for 15 multidegrees: r=0, zero vectors, (1), (2), (3), (1,1), (0,1), (2,1), (1,2), (2,2), (1,1,1), (0,1,1), (1,2,1), and (1,1,1,1). It checked boundary squares, transpose ranks, and all homology dimensions against the displayed formula. The results agree: zero multidegree contributes in degree zero, squarefree nonzero multidegrees in total degree, and nonsquarefree multidegrees are acyclic. This is evidence for the edge cases in addition to the written proof, not a compiler or a replacement proof.
