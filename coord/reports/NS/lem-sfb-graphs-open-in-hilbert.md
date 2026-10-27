# Worker report: lem-sfb-graphs-open-in-hilbert

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-graphs-open-in-hilbert.json`: statement; split into six proof steps, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-universal-isomorphism-open.json`: new statement-only unsplit node; scheme specialization of Stacks Tag 05XD; no Mathlib match.
- `citations.json`: verbatim statement quotations for every step citation.

One new node, zero Mathlib leaves. No unit record changed: this item is not the unit's key statement.

## Attachments

None. Searched the live project's `lean/WeilConjectures/` both by item tag and by graph, Hilbert, Mor-into-Hilb, and isomorphism-locus notions. The finite-etale clopen-graph theorem and Hilbert-of-points constructions have different hypotheses and conclusions. The maximal isomorphism open of a map lies in that map's target and does not give the universal parameter-base open needed here. Neither the item nor the new general result has a matching project declaration.

## WANTED

None. Both source files used are present under `literature/stacks-project/`.

## Corrections and scope

The live item had no proof. Its statement is mathematically correct: no hypothesis or conclusion was changed. I added the missing definition citation `[def-weil-closed-immersion]` for its existing closed-subscheme notion, and added that same definition to stmt_deps. The proof now handles arbitrary separated X, without imposing finite presentation or flatness on X or Noetherian hypotheses on the base.

Read the chapter record, the inherited unit record `sk-thm-sf-ctf-stability`, and the item's ancestry. The item's existing ancestry describes the de Jong 3.9 graph construction used in the alteration route for direct-image finiteness. The split serves that same subargument. `blueprint_refs.py ancestor` reports `None`: the live ancestry already has a null from.node. I preserved that field and the existing via list, and inherited it faithfully for the new node by prepending the item. No blueprint update appears on this item; no unit or chapter route was replaced.

## Not duplicates

No existing node carries Tag 05XD or `spaces-more-morphisms-lemma-where-isomorphism`. Searched the whole DAG by the tag, source label, universal closedness, isomorphism locus, graph, and Hilbert terms; searched the whole imported blueprint with `blueprint_refs.py search` for `05XD`, `where-isomorphism`, `isomorphism locus`, `universally closed`, `graph`, and `Hilbert functor`. Read the existing proper/flat/finite-presentation permanence statements and reused them.

`lem-sfb-universal-isomorphism-open` is a theorem about an arbitrary map between two families, with the six hypotheses of Tag 05XD. It mentions no graph, closed family in a product, Hilbert functor, or morphism functor. It supplies the non-elementary open-locus theorem used in one step, while the item's steps prove closedness and recovery of graphs, naturality, the fibre-product representation, and evaluation. It does not merely restate the item's open-immersion assertion. The existing `lem-sfb-projective-curve-isom-graphs` instead concerns representing the Isom functor for projective curve families and depends on graph/Hilbert machinery; it cannot supply this general isomorphism-base-change locus. The finite locally free module isomorphism-locus nodes concern module maps rather than scheme morphisms. No new node duplicates the already-existing graph or permanence facts.

## Review by NS

I read quot.tex, `lemma-Mor-into-Hilb` and `lemma-Mor-into-Hilb-open` (Tags 0D1A and 0D1B), including their proofs. I followed their route: graphs first, then the first-projection isomorphism criterion, then the universal open locus. For the new node I read spaces-more-morphisms.tex, `lemma-where-isomorphism`, Tag 05XD, including its full statement and proof. Its six hypotheses are copied, specialized to schemes, without adding flatness of the target family or an assumption on f itself. The source obtains its open by intersecting the universal surjective-flat and closed-immersion opens. This substantial general result is left as a statement-only node, not reproduced as an unexplained assertion inside the item's proof.

For step 1, I opened and read the statements of `lem-weil-pbc-proper-fp-permanence`, `lem-weil-pbc-flat-morphism-base-change`, and `lem-weil-pbc-qcqs-morphism-permanence`. Respectively, clause (b) provides both proper and closed-immersion base change; the flat node gives flatness after arbitrary base change; clause (3) of the qcqs node explicitly supplies finite-presentation base change. I also read `def-weil-proper-morphism`, which really defines separatedness by the closed diagonal, and `def-pc-fibre-product`, whose universal property proves the displayed graph square is cartesian. Thus graph closedness is a two-line diagonal pullback argument from those statements; it is not an additional lemma hidden under an uncited graph theorem. The graph's domain is the actual scheme Z_T, so its structure map has the required properties. A closed immersion need not itself be finitely presented, and I never assert that it is.

For step 2, the same three permanence statements apply to the actual pullback D_{T'} of any admissible family. The fibre-product definition supplies the canonical iterated-pullback identifications and the uniqueness identifying the pulled-back graph with the graph of the pulled-back map. No descent, proper image, or representability theorem is being inferred from a definition. I marked this step non-elementary because it applies the permanence lemmas.

For step 3, `def-pc-fibre-product` suffices: the two component equations give j = Gamma_f composed with k. This proves the converse graph criterion scheme-theoretically, rather than inferring it only from underlying points. Its first-projection inverse recovers f, giving actual injectivity. This is elementary and does not create a node for one clause of the item.

For step 4, I checked all six hypotheses against the statement of the new node. D -> T is flat and locally of finite presentation by Hilbert membership, and universally closed by its assumed properness. Z_T -> T is proper by step 1, hence is separated, locally of finite type and closed on underlying spaces. These implications are explicitly in `def-weil-proper-morphism`, whose finite-type notion contains local finite type and whose universal-closed condition includes the identity base change. Crucially the open is in T, not in Z_T, and the criterion is for every T' -> T, including nonflat and nonreduced tests. No part of the cited node's proof is used as an extra conclusion.

Steps 5 and 6 use the already-proved graph criterion to identify each test-scheme fibre of the functor pullback with maps into U. The pair consists of a base map h and a unique f, not merely a point in the set-theoretic image. This explicitly proves the required open-immersion representability. For a representing Hilbert scheme I apply this to its universal family, giving an actual open representing scheme and evaluation. I wrote the equality of the pullback of k^{-1} with the inverse of the pullback of k by its two inverse equations, so arbitrary-base-change compatibility is justified, rather than claimed by the word 'transport'. These are elementary consequences of the preceding steps; they introduce no new substantial lemma. Each proof step is shorter than 2000 characters.

I tested small cases: Z empty gives a unique morphism and only the empty family; D empty gives the open on which Z_T is empty. If both families in 05XD are empty, its open is the whole base. If the target family is empty, existence of f forces the source empty. For a fixed field base a non-isomorphism gives the empty open, whereas an isomorphism gives the whole base. Over k[epsilon]/(epsilon^2), multiplication epsilon -> 0 on the dual numbers has an isomorphic reduced fibre but is not an isomorphism: this is not a counterexample to 05XD, since the source scheme of that map is not flat over the dual-number base. This checks that the flatness hypothesis is essential and was retained. In the graph argument nonreduced test schemes are treated through scheme-theoretic inverse equations, not through a fibrewise point criterion. No statement dispute was found.

I checked delivery-errors B--E throughout: complete standalone new statement, all notions defined by cited definitions, exact tag and source label, no proof in the unsplit node, no circular dependence, no new node for an elementary graph argument or for an existing permanence statement. citations.json quotes the statements actually read. All Mathlib searches in the new node were run with msearch.py, with exact tool/query strings and returned records retained in searches.jsonl. Both semantic phrasings were tried, as well as Loogle and source grep. The hits on universally open maps, fpqc descent, stalk maps, and functor gluing fail the needed universal isomorphism-locus statement. No search outage was reported.

## Unfinished work

Only the new statement-only node remains to be split in a later item. The six-step proof of this item is complete relative to its cited statements. The required server dry run and push are performed after this report is written.
