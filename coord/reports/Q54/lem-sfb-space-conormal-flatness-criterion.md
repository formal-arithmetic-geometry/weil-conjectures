# Stage-1 report: lem-sfb-space-conormal-flatness-criterion

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-space-conormal-flatness-criterion.json` (statement; split by reuse of an existing equivalent criterion), `citations.json`, and this report. No new nodes; no Mathlib leaves. Mathlib searches are preserved and the additional actual searches are recorded from searches.jsonl.
2. Attachments: none. Searches in lean/WeilConjectures by the exact blueprint tag and by conormal/flatness found no declaration proving every clause. The closed-immersion conormal flat-base-change declaration concerns schemes and only the base-change direction, so it is not an attachment.
3. WANTED: none.
4. The imported item has an equivalent existing DAG node, `lem-sfb-space-square-zero-flatness-criterion` (also Tag 06BH). I reused it instead of duplicating the theorem or creating a new node restating its clauses. The item statement is unchanged. The existing node is unsplit: the present split delegates the shared theorem to that existing queue item, rather than claiming its Lean proof is finished.
5. Nothing remains unfinished in this one-level split. No Lean or compiler commands were run and the shared repository was read only.

## Not duplicates

No new nodes. The item and `lem-sfb-space-square-zero-flatness-criterion` express the same equivalence: square-zero conormal quotients are the ideal modules. The proof cites that existing node; no duplicate node was created. A dependency traversal found no path back from it to this item.

## Source error

The proof of Stacks Tag 06BH, spaces-more-morphisms.tex, lemma-deform, prints $U=V\times_{V\prime}V\prime$ when testing the Cartesian square. The correct expression is $U=V\times_{V\prime}U\prime$. For example take identity thickenings $Y=Y\prime=\operatorname{Spec}k$, $X=X\prime=\mathbb A^1_k$, and identity atlases. The original square is Cartesian, but the printed right side is a point, whereas $U$ is the affine line. This is a proof typo, not a false theorem or a change to the item statement. I also read the scheme analogue Tag 063Y, more-morphisms.tex, lemma-deform: its affine ideal calculation confirms the same ideal criterion and imposes no Noetherian hypothesis.

## Review by Q54

I read Stacks Tag 06BH's statement and proof and Tag 063Y's statement and affine proof. The item is exactly the algebraic-space statement. I read the chapter and unit records, checked the three blueprint levels, and searched literature/blueprint/latest and the whole imported blueprint for conormal, Tag 06BH, and square-zero flatness; no imported blueprint node states this theorem. The inherited blueprint place already locates the supporting Tag 06BH input, and I retained it and recorded which part the two steps realize. There is no change to the unit route.

For step 1 I checked that quotient by the zero submodule has the explicit identity inverse and that the ideal action factors through the quotient structure sheaf because the square of each ideal vanishes. The map comparison is on local tensors and respects restriction, so it proves equality of the sheaf maps, not merely equality of their sources. The lift-independence calculation uses commutativity of the given square to put the image of j in the source ideal. This is a direct use of the definitions, not a separate hidden theorem. Neither X nor Y is assumed reduced; the step uses their small etale sites.

For step 2 I opened and read the full statement of `lem-sfb-space-square-zero-flatness-criterion`. It explicitly gives both implications for algebraic spaces over any scheme S, on the small etale sites, with square-zero ideals and flat f. Its flat and Cartesian conjunction is exactly the desired one, and its tensor definition is the same as the item's. It has no finite-presentation, Noetherian, or additional flatness hypothesis. All these hypotheses therefore match under Z=X. The canonical Cartesian comparison, rather than an unspecified isomorphism of spaces, is used. citations.json quotes verbatim the whole used equivalence. Both nodes have the same unit, so no off-unit tool declaration is needed.

I checked B1–B10: there are no fresh unsplit nodes, no missing-object statements or new tags, all searches were run with the required command, and the existing source and blueprint fields were retained. For C1–C8, the sole non-elementary fact is the existing cited criterion; its statement, not its proof, supplies exactly the equivalence. For D1–D5, no content was moved to a newly named copy: the DAG reuse rule deliberately avoids splitting an already present theorem twice. For E1–E7 I checked zero ideals, empty spaces, identity morphisms, nonreduced X and Y, and arbitrary square-zero modules. With zero ideals the conormal map is 0 to 0 and f'=f; with identity morphisms it is the identity map. None require finiteness. No step exceeds 2000 characters. The source typo above is the only correction identified.
