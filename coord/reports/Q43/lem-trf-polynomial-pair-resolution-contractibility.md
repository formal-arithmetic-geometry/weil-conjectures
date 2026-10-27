# Q43 stage-1 delivery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-polynomial-pair-resolution-contractibility.json`: item, split into seven proof steps. Mathlib searches found no declaration proving the entire item. Added the existing polynomial-ring definition/universal property to `stmt_deps`.
- `citations.json`: thirteen verbatim excerpts, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log.

No new nodes; no Mathlib leaves created; no Lean written or compiler invoked.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the blueprint id, PolynomialPair/polynomial_pair/polynomialPair, polynomial resolutions and trivial Kan terminology. No declaration states the item. The sorry-free homotopy-equivalence helper is reused through its existing node, not reported as an attachment of this different item.

## Wanted

None. All mathematical sources used are present.

## Problems found and changes

The item was statement-only, not previously split or reviewed; no released repair note exists. Its statement is correct as written. The opposite-category variance of the source site is already corrected in the item: Stacks calls U cosimplicial in its site and uses Mor(U_bullet,W), while our ordinary algebra-map category uses the simplicial Hom(W,U_bullet). No further change is required.

The direct assumption that both augmentations are trivial Kan fibrations makes the final polynomial-extension proof of 08QV unnecessary here. In particular, the existing polynomial-extension lemma is not used backwards to infer a quasi-isomorphism from these hypotheses. Likewise the larger `lem-trf-polynomial-presentation-homology` is not used for its proof or for a clause it does not state about pairs.

No statement dispute, source error affecting this item, or route departure was found. The latest blueprint's contracting-correspondence proof remains the ancestor route; this is an inherited auxiliary cotangent-complex computation below that route, not a replacement of it.

## Unfinished work

None within this one-level stage-1 split. The generic homotopy-equivalence theorem is already present as a reviewed node. All remaining operations in this item are explicit universal-property, functoriality, or coordinatewise boundary-lifting arguments.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs. Whole-DAG searches by polynomial presentation, contractibility, trivial Kan, 08NS and the source labels identified the existing polynomial universal property, trivial Kan definition and homotopy-equivalence node. Blueprint-reference searches for `contractib`, `polynomial` and `trivial Kan` found no blueprint node stating this pair-category result. The single-presentation homology node has one polynomial source, not a pair of polynomial sources, and a separate derived-colimit conclusion; it does not state this item.

## Review by Q43

I read Stacks `cotangent.tex`, Tag 08QV (`lemma-polynomial-on-top`), from the construction of U through the generator-product and fibre argument, and `simplicial.tex` Tags 08NN (`lemma-trivial-kan-base-change`), 08NR (`lemma-product-trivial-kan`) and 08NS (`lemma-trivial-kan-homotopy`). I read the latest blueprint `sec-trace-formula/sk-i-curve-zero/_section.md` and `lem-trf-local-term-locality.proof.md`, along with the recorded unit and chapter. The ancestor's current proof concerns contracting correspondences; the inherited chain in the item's blueprint field explains the auxiliary polynomial-top input. I retained that chain and statement.

For Step 1 I opened the statements of `def-weil-pbc-mv-polynomial-ring`, `def-trf-polynomial-presentation-pair-categories`, and `def-weil-pbc-simplicial-object`. The first explicitly supplies existence and uniqueness of evaluation; the second specifies commuting augmentation-preserving algebra-map pairs; the third fixes the contravariant simplex operators. Thus extending each operator fixing E and testing its augmentation and composition on coefficients and variables proves the claimed functor, without any preservation-of-polynomial-presentation assertion about its maps.

For Step 2 the item assumes a bounded generator presentation for each P_n, and the size and pair-category definitions specify bounded representatives. The displayed conjugation, its cancellation law, and postcomposition on Hom are the actual argument for transport, rather than a bare claim of transport. Generator sets for the second polynomial extension are E, already within the common bound. No chosen presentations are required to be compatible before conjugation.

For Step 3 I checked that the pair-category statement really gives Q tensor_P B = B[T] and the induced morphism commuting with coefficient specialization. Here T is E and its augmentation is e maps to X_e, so the target is the identity-augmented C. The universal-property statement says agreement on variables implies equality, giving the identity on every operator. The explicit coefficient and variable formulas pin the advertised canonical tensor isomorphism; no general tensor-commutes-with-resolution theorem is used.

For Step 4 I checked again both polynomial universal-property clauses and the pair morphism definition. The lower map is determined by the S coordinates; its composite into P_n[E] is the prescribed coefficient map for constructing the upper map from the T coordinates. Compatibility with gamma on the coefficients follows from beta and the A-to-B-to-C compatibility; on T it is exactly the prescribed fibre condition. Naturality is written as the action on both coordinate families, so this is an isomorphism of simplicial sets, not merely degreewise bijections. The inverse is constructed in the step, not extracted from the proof of another node.

For Steps 5 and 6 I opened the complete statement of `def-weil-pbc-trivial-kan-fibration`: it requires surjectivity in degree zero and boundary lifting for every positive n. Step 5 verifies both for a fibre by applying the given augmentation to a constant simplex of value d. Step 6 verifies both for an arbitrary set product by projecting and choosing fillers coordinatewise; no finite-product restriction is introduced. These are short direct uses of the defining lifting condition (the elementary exception in the brief), not uncited non-elementary base-change or product theorems. I therefore did not create nodes for Stacks 08NN or 08NR or cite the tags as black boxes.

For Step 7 I opened `lem-weil-pbc-trivial-kan-homotopy-equivalence` and verified that its statement explicitly gives a section g and a cylinder homotopy from the identity to gp, hence exactly the required simplicial homotopy equivalence. Its sole hypothesis, that p is a trivial Kan fibration, is established by Step 6. This generic theorem is outside the item's unit and is declared in `split_report.tool_uses`; it is precisely the abstract 08NS tool used by the source, and no statement in the unit replaces it.

I tested empty S and T (the mapping set is the singleton of the structural pair), E empty (upper target is P_n and no added-variable argument is needed), and infinite S,T,E (polynomial evaluations have finite monomial support and the product filler uses choice indexed by a set). I also checked B and C zero rings: the argument uses only the assumed trivial Kan maps and their specified fibres, never cancellation, faithful flatness, or nonzero coefficients. For n=0, the separate surjectivity check supplies a vertex; for n>0, constant base simplices force all fillers into the correct fibre. The formula works for nonsurjective A-to-B; only the two explicitly assumed simplicial augmentations supply lifts.

Against delivery-errors B--E: no new statement-only node or duplicate is introduced, every notion and non-elementary theorem used has its defining/result node, each citation quote is copied verbatim, and every non-elementary use is the statement of the cited node. No clause is moved into a renamed helper. No dependency points back through the polynomial-top parent. All steps are below 2000 characters; none conceals an induction, comparison lemma, or deferred argument. Only the final step invokes a non-elementary theorem. All other steps give the requested construction or direct short defining-property check in place. Searches were executed through the required msearch command, with two different semantic phrasings, Loogle, LeanSearch and grep; recorded queries/results are those actually returned. The historical item searches were retained.
