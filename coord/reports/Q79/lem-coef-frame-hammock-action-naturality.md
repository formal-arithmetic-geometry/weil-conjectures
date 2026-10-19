# Stage-1 report: lem-coef-frame-hammock-action-naturality

## Files written

- `dag/nodes/sec-six-functors/lem-coef-frame-hammock-action-naturality.json`: statement node, now split into seven proof steps; no Mathlib match.
- No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim statement extracts for every proof-step citation.
- `searches.jsonl`: actual msearch results. The existing node's earlier searches are retained, and the new queries and results have been added to its Mathlib searches.

## Attachments

None. Searching the read-only slopmaster2 `WeilConjectures/` tree for the exact item id, its blueprint tag, and `hammock`/`Hammock` gave no declaration. Thus there is no exact project attachment, and no purported finished master proof has been used.

## Literature

Read online: [Zhen Lin Low, Revisiting function complexes and simplicial localisation](https://arxiv.org/pdf/1409.8062), Definition 3.1, Lemma 3.4 and Proposition 3.7(ii), printed pp.12–15; and [Hinich, Dwyer–Kan localization revisited](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hinich.pdf), Section 1.2, printed pp.5–6. Low's proof uses model-category pushouts for its special resolutions. I did not apply that theorem under the weaker hypotheses here: the proof is marked agent-written and explicitly constructs the padded-row homotopies, using only the hammock construction.

WANTED: Low, Revisiting function complexes and simplicial localisation, arXiv:1409.8062, Definition 3.1, Lemma 3.4 and Proposition 3.7(ii), for lem-coef-frame-hammock-action-naturality (local archival copy; read online).

WANTED: Hinich, Dwyer–Kan localization revisited, Section 1.2, for lem-coef-frame-hammock-action-naturality (local archival copy; read online). The proof uses the already existing hammock nodes for its mathematical inputs; this request is archival.

No Stacks tag states this hammock comparison, and none is invented or used. No SGA source is used.

## Audit and corrections

The item was statement-only, with no finished Lean declaration or proof to reuse. Its statement is unchanged. It correctly distinguishes weak augmentations from Reedy resolutions and does not assert that its comparison map is a weak equivalence.

The essential missing argument was endpoint naturality. Directly stacking the shorter zigzags would put c or d on the endpoint columns, which is not an allowed hammock. Step 5 instead uses word `+ - + -` with c internal; step 6 uses `- + - +` with d internal. The two-out-of-three calculation proving c,d belong to W is written before those constructions. The degreewise products with the interval give actual simplicial homotopies, rather than only paths for individual vertices.

Read the chapter and unit records and the current main-20261015 ancestor `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.md`. That current ancestor file states the coefficient adjunction but has no detailed proof; the inherited blueprint ancestry records the detailed parent frame-comparison location. This delivery preserves that ancestry and the maintainer-owned unit binding. It supplies the same localization-action argument used by the parent, without changing the chapter or unit route. This is not a unit key node, so no unit realization fields are changed.

The off-unit generic tool `lem-cbc-simplicial-homotopy-equivalence-weak` is declared in `split_report.tool_uses`. It is used solely to invert the interval projection in Ho(sSet), not to replace a step of the coefficient-adjunction route.

## Not duplicates

There are no new nodes. Whole-DAG searches for hammocks and simplicial homotopies found the existing reduction and simplicial homotopy-equivalence nodes used below. Whole-blueprint searches `hammock` and `weakly augmented` found no equivalent blueprint node; `same_as` is empty. The item is not the general reduced-hammock construction or the assertion that composition by an inverted arrow is a weak equivalence: it constructs the particular index-forgetting maps and their comparisons.

## Review by Q79

I read the complete statements of every cited node. `lem-coef-hammock-infinity-localization` explicitly supplies reduced hammocks with downward W-arrows and identity endpoint arrows, row deletion/repetition followed by reduction, concatenation, and the ordinary nerve convention. `lem-coef-hammock-graph-colimit-presentation` explicitly allows fixed-word unreduced grids, identifies their reduction with the reduced mapping set, and states naturality for functors of pairs, including simplicial operators. `lem-cbc-simplicial-homotopy-equivalence-weak` gives weak equivalence from the two specified simplicial homotopies with no Kan or nonemptiness assumption. These statements, not arguments hidden in their proofs, are what the steps use. The exact extracts are in citations.json.

Step 1 is the category-law calculation and two-out-of-three, written out. In particular beta has type [n'] to [n], so Q(beta) has exactly the direction Q_n to Q_n'; composition of the beta indices reverses as specified. The augmentation equations really imply both interior vertical arrows are weak equivalences; this does not require a lifting property.

Step 2 uses the hammock and reduction statements just described. The middle square is precisely the defining equation of I, the outer squares are augmentation naturality, and the two exterior horizontal arrows are the assumed weak equivalences. Its row-operation calculation verifies a simplicial map, including degenerate grids. Step 3 uses the reduction node's stated functoriality, which covers a functor creating extra identity columns; it does not assume such a functor preserves reduced diagrams before reduction. The resulting relative-functor square is strictly commutative.

Step 4 explicitly proves both endpoint maps are weak equivalences, and checks that h maps to b h a as a functor rather than just an object function. Its intermediate h maps to h a uses the weakly augmented pair (P',Q), to which steps 1 and 2 apply with endpoints (x',y).

For step 5 I checked each vertex column of the two displayed rows. The endpoint columns stay x' and y, with identity vertical arrows. At the changing row the internal maps are c, a followed by the P' structure map, and the Q structure map. The p a = c p' equation checks the left square, naturality of a and the I equation check the central square. Every internal vertical arrow belongs to W by step 1, step 4 and closure under composition. For a deleted row spanning the change, a_l U'_{j,l} = U_{j,l} a_j is exactly naturality, so this construction works on all simplices, not just vertices. The cited hammock and reduction statements provide precisely the interpretation and reduction used here.

For step 6 the endpoint columns instead stay x' and y'. The new internal maps are the P' structure map, b followed by the Q structure map, and d. The equation b i = i' d is the required right square. The mixed central square also uses naturality of a, as explicitly written; no unmentioned compatibility of b h a is assumed. Naturality of b verifies row deletion across the change. At the two endpoints of the interval the rows reduce to the two stated maps. Again the cited hammock and reduction statements have exactly this scope.

Step 7 uses the homotopy-equivalence node with r the interval projection and j_0 its section. The first inverse equation is strict, hence has a constant homotopy. The other homotopy is the explicit vertexwise minimum formula; it is monotone and commutes with all restrictions. Thus the cited theorem applies to arbitrary small K. Inverting r forces both interval sections to be its inverse, so homotopy endpoints agree in the localization. Postcomposing step 5 with d and using step 6 yields the desired equality. Concatenation here is the enriched composition explicitly supplied by the cited hammock node.

For B1–B9 there are no new node statements, leaves, tag collisions or hidden proof sketches to audit. Existing statement/metadata and ancestry are preserved. For C1–C8 I checked every non-elementary input against its actual cited statement, declared the sole off-unit tool, and checked dependency closures of all three proof inputs: none reaches the item. For D1–D5 the argument remains in this item; no clause has been moved to a replacement node. Each comparison is an explicit commutative grid, not an appeal to the desired naturality itself. Every proof step is below 2000 characters, and I checked that no step hides a separately stated comparison lemma: the row constructions are the direct argument for the item's own two comparisons.

For E1–E7 I tested the following small cases. With W consisting of identities, the structure and comparison maps in W are identities and the displayed prisms reduce to constant maps; all category-index copies remain allowed. In the terminal category every horizontal column can disappear, leaving the allowed length-zero identity. If the Hom sets are empty, I and its nerve can be empty: the constructions and interval-projection theorem still apply, with no illicit chosen vertex. Nonidentity endpoint endomorphisms c,d remain internal to the padded rows, so no equality c=1 or d=1 is used even when endpoint objects coincide. A relative functor collapsing nonidentity arrows is covered by naturality of reduction, not by an assumption that the unreduced shape survives unchanged. No statement dispute or changed hypothesis resulted from these tests.

The self-review corrected the tempting invalid endpoint-column comparison by the padded rows before the file was written. No second worker was started, as the direct-delivery brief requires. Nothing was written to either source checkout or the shared repository, and no Lean/compiler/Lake tool was run.

## Unfinished work

None in this one-level split. Independent maintainer review remains the receiving side's responsibility. Server dry-run and delivery outcomes are recorded by the required delivery command.
