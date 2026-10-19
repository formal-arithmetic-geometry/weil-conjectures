## Files written

- `dag/nodes/sec-six-functors/lem-coef-small-inner-horn-completion.json`: statement, split into eight proof steps; no exact Mathlib match for the complete explicit construction and its universe and strict restriction clauses. Existing Mathlib leaves supply the cell-class and pushout-product theorems.
- `citations.json`: twelve verbatim citation entries, one for every step/node pair.
- `searches.jsonl`: six searches actually run through msearch.py, including two semantic phrasings. The inherited item's earlier Q110 searches are retained in its JSON; the new Q35 searches are appended verbatim from this log.

New nodes: none. New Mathlib leaves: none.

## Attachments

None. Searches for the exact blueprint tag, small-inner/horn-completion names, inner horns, innerAnodyne and quasicategory terminology under the read-only project `WeilConjectures/` source found no declaration stating this item. The upstream master source was also searched as reference only. No Lean was written or compiled.

## Sources wanted

WANTED: archived Higher Topos Theory, proof of Corollary 2.2.5.4 and Corollaries 2.3.2.4–2.3.2.5, for lem-coef-small-inner-horn-completion.

WANTED: archived Kerodon Proposition 4.1.3.2 and Corollary 4.1.3.3 (subsection 01BM), and Proposition 1.5.7.6 (00J9), for lem-coef-small-inner-horn-completion.

The available web search result returned the full construction and finite-horn argument of 4.1.3.2, and the full pushout-product proof of 1.5.7.6. Direct subsequent page requests failed/returned no text; no local archival copy was downloaded. The proof is therefore marked agent, tied to the existing blueprint ancestry, with the online sources named per step. Its two non-elementary mathematical inputs are existing pinned Mathlib leaves, whose source was read locally.

## Corrections and scope

The imported item had no proof. Its statement is unchanged: no additional hypothesis, weakened conclusion, replacement of the actual restriction, or new universe-specific completion. I made the degreewise quotient, horn factorization, exact exponential formulas and strict diagonal explicit. No statement dispute was found.

Read the chapter and unit records and the current main-20261015 ancestor proof: paragraph 2 of `prop-coef-integral-exceptional-adjoint.proof.md` contains the coefficient-adjunction calculation which this foundational dependency serves via step 3 of `lem-coef-cat-infinity-colimits-cartesian-closure`. This is a split below the unit route, not a new geometric or coefficient route. No SGA source is used. No chapter/unit record or maintainer field was changed.

## Not duplicates

No new node is proposed. Whole-DAG searches for inner-anodyne, inner-horn, small-object and transfinite-cell terminology found `lem-coef-inner-horn-cell-generation`, already a Mathlib leaf, and `lem-coef-inner-anodyne-pushout-product`, also a Mathlib leaf. They are cited instead of duplicated. `lem-cbc-internal-hom-quasicategory` states one conclusion needed here, but the short product-horn application already proves it from the pushout-product leaf, so a separate off-unit citation is unnecessary. Generic small-object factorization nodes provide existence rather than this specified countable replacement. Blueprint searches for “small inner horn completion”, “inner anodyne” and “horn” found no blueprint statement of the item; `same_as` is empty and the existing precise ancestry is preserved.

## Review by Q35

I read delivery-errors B–E, the whole item statement, the three cited statements and the source text of Mathlib `Inner/Basic.lean:38–53,80–98` and `Inner/PushoutProduct.lean:103–109`. `innerAnodyneExtensions` is the left lifting class of inner fibrations at line 43. The cell-generation equality at lines 89–92 is exactly the existing node's equality of classes, with continuous ordinal composites, small coproducts and pushouts. The pushout-product theorem is the existing node's lifting-class theorem for a degreewise monomorphism, not merely a statement about weak equivalences. The online Kerodon construction attaches all squares simultaneously, takes a countable union and factors each finite horn through a stage; setting its target to a point gives precisely this item's construction. Its functoriality is relabelling, as written here. Kerodon 1.5.7.6 uses the same union of two products as step 7. No clause from the proof of another DAG node is being used without its statement saying it.

Step 1 uses the definition node for simplicial sets and horn inclusions. The quotient description gives actual degreewise pushouts and proves injectivity; it does not assume an arbitrary pushout of sets preserves both legs. A horn simplex in an attaching copy is identified with its one old image, so no two distinct old simplices become identified. Operators descend because the attaching maps are simplicial. The attaching labels are a subset of a countable product of function sets; all coproducts are small, and the countable union is small. This is an explicit set construction, not an unproved small-object theorem. There is no extra node for this elementary unpacking.

Step 2 uses exactly the definition node's assertion that a horn is the union of all faces except one. There are finitely many such faces, each generated by its top simplex; taking a maximum stage contains their entire images. The injection established in step 1 ensures that their overlaps agree already in that stage. Thus the attached labelled simplex gives the filler. This avoids assuming that the horn has finitely many simplices in every degree combined, and avoids an uncited compactness theorem.

Step 3 again uses the horn and simplicial-map definitions only. I checked the map on each glued horn, the indexing of the target cell, the stage-inclusion compatibility, and both identity and composition on all cells. No choice of filler is used to define R(f).

Step 4 cites the cell-generation node's stated equality of classes. The countable presentation is an admissible transfinite presentation, and the identity arrow retract is allowed. Crucially the theorem is instantiated in each test universe: the same small cell presentation remains small there. It therefore proves lifting against larger inner fibrations, rather than inferring that incorrectly from small-universe lifting. The pushout-product node explicitly defines inner fibrations and the lifting-class convention; the map from E to a point is such a fibration exactly because E is a quasicategory.

Step 5 uses the internal functor simplicial set definition, not a fully faithful Yoneda assertion. Both adjunction formulas are written down in every degree; the variable theta is an arbitrary simplex of Delta^m. Naturality proves that they are inverse and commute with restriction, so it applies to arbitrary parameter simplicial sets P and Q in the next steps. The argument is elementary from that definition.

Step 6 uses the full stated pushout-product theorem, first with an inner horn inclusion (inner anodyne directly by the definition of inner fibration) and the monomorphism from the empty set to K. The result is the horn times K, up to the explicit factor swap. Lifting into E and step 5 provide every inner horn filler for Fun(K,E); no hypothesis that K is itself a quasicategory is used. This supplies both asserted quasicategory objects, including Fun(X,E) when X is not fibrant.

Step 7 uses the pushout-product statement with i=j_X and j=u. Step 4 proves its first hypothesis in precisely the universe where P,Q,E live; u supplies its second hypothesis. The square adjoints to maps on RX times P and X times Q agreeing on X times P, exactly the domain displayed in the cited node. A lift into E gives an actual map RX times Q to E. Both restrictions, hence both triangles, are strict equalities. No passage to homotopy classes, cores or equivalence categories is substituted for the required restriction map.

Step 8 uses only the same definitions and the two lifting results already applied. Set-theoretic enlargement does not introduce new functions between the fixed input sets, so it does not change the labels or maps. Reapplying both general theorems in the larger universe covers genuinely larger tests. For empty X, all indexing sets of horns are empty since n is at least 2 and horns contain vertices. Thus RX stays empty. I also checked n=2,i=1 (two edges with a common vertex, whose images lie in the maximum of two stages), monomorphisms with P empty, and Q empty (then P empty), and E empty. For nonempty X no square into the empty target exists; for empty X the restriction is the identity of the point. There is no unintended nonemptiness assumption in the quasicategory convention.

B1–B10 require no new-node repairs because none is introduced. C1/C4 are addressed by the per-step statement checks and the verbatim citations file; C3 is addressed by never using a cited proof as an interface. All proof citations are definitions or existing Mathlib leaves, so no undeclared off-unit tool is involved. D1/D2 are avoided because the construction and lifting argument are in the item's own steps. I checked E's hypotheses and the edge cases just described. All eight steps are shorter than 2000 characters; the elementary ones each unpack the specified quotient, face cover, relabelling or evaluation formula, and contain no separate standard comparison lemma. No unresolved mathematical or source-statement fault remains.

## Unfinished work

None in the stage-1 split. Archival source copies remain wanted as listed above. Delivery awaits the mandatory server dry run and push.
