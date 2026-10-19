1. Files written:

- `lem-coef-hocolim-value-diagram-naturality.json` — statement, split proof, no new nodes.
- `citations.json` — verbatim citations for every cited step.

2. Attachments: none.

3. WANTED: Dugger, *Combinatorial Model Categories Have Presentations*, Appendix A.2 and Remark A.3(i)-(iii), printed pp. 197–198, for the projective-replacement naturality calculation; the URL is recorded in the node but the document is not archived under `literature/`.

4. The imported statement is well typed and was retained exactly. The imported proof was empty, so I supplied the three arguments needed: functorial projective replacements induce the map (H_K(\eta)); the localized colimit cocone universal property identifies the two composites after restricting along (g); and the identity case follows by substitution. I searched the source tree for the blueprint tag and for hocolim/value-diagram declarations; no Lean declaration states this item, and no duplicate blueprint node was found. The existing `lem-coef-model-colimit-localization-comparison` statement supplies projective replacements and the localized cocone universal property, while `lem-coef-hocolim-reindexing-zigzags` states the canonical reindexing comparison. No new node is a clause of the item.

## Review by Q23

I read the item node, its unit `sk-prop-sf-biduality-general`, the blueprint proof paragraph named in the node, and the complete statements of both cited nodes. Step 1 uses exactly the model-colimit node's projective diagram model structure and its localized colimit cocone; the remaining passage from a chosen functorial replacement to `colim Q(η)` is the definition of the induced map. Step 2 uses the model-colimit node's explicit assertion that the cocone maps and universal property are included, and the reindexing node's statement of the canonical `g_*`; naturality of `η` makes the restricted cocones commute. Step 3 is an elementary identity specialization of the displayed equation. I checked the hypotheses: (K) and (J) are small, (g) is a functor, and `η` is objectwise a weak equivalence as required by the item; no extra cofibrancy or fibrancy assumption was introduced. I tested the identity-indexing case, the zero natural transformation between zero diagrams, and empty indexing categories (where the colimit cocone is initial); the equation remains the universal-property equality in each case. The statement is unchanged and no duplicate or attachment was found.
