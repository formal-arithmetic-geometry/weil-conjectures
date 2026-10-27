# Q68 — lem-sfb-field-groupoid-constant-local-dimension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-field-groupoid-constant-local-dimension.json`: existing statement, now split in four elementary steps using two existing nodes. Mathlib searches found no exact theorem or one-line specialization. No new nodes and no new Mathlib leaves.
- `citations.json`: a verbatim statement quotation for each step/node pair.
- `report.md`: this report. `searches.jsonl` is the unmodified output log of msearch.py; `write_split.py` is sandbox-only preparation code.

## Attachments

None. Searched the exact blueprint tag and the concepts field groupoid, groupoid dimension, constant local dimension and equidimensionality in `lean/WeilConjectures/`. The constant-local-dimension component and equidimensional-open declarations concern schemes with an assumed dimension condition; they do not establish the item for algebraic-space groupoids. There is no project Lean declaration of this item to attach.

## WANTED

None: all sources used are present locally.

## Corrections and dependencies

The statement and its six statement dependencies are unchanged. There was no proof to retain in the sandbox or in the live node. The chapter and unit records were read, followed by the current blueprint unit and direct-images proof under `literature/blueprint/latest/`. The unit record is historical (its chapter field names sec-six-functors); the item belongs to sec-six-functors-basics. Neither record was edited. The specific inherited blueprint place and ancestor-null chain are preserved. Whole-blueprint searches for groupoid, groupoid dimension, homogeneity and two fibres found no equivalent statement. DAG source/statement searches also found no existing pointed source-fibre transport theorem.

There are no proposed new nodes: the source-fibre transport initially considered as a lemma fits into a few lines of explicit groupoid identities, so delivery-errors B/C/D and the no-elementary-new-node rule require keeping it in the proof. The only substantial dimension input is the existing scheme base-change theorem. Existing algebraic-space field-extension nodes impose separatedness, quasi-separatedness, finite type or assert only global bounds; those hypotheses are absent here. They are not used. In particular no topological-dimension/atlas-dimension comparison for decent spaces is needed: all algebraic-space dimensions are chart dimensions, exactly as in the statement and Tags 04N5/04N6.

## Source error

The local source `spaces-more-groupoids.tex`, Tag 06FD, proof of (1), asserts that restriction of a field groupoid along any field extension preserves its point dimensions, since it is two field base changes. This assertion is false. Take the identity groupoid U=R=Spec(k), with s=t=id, and extend to k'=k(T). Its restriction has arrow scheme R'=Spec(k' tensor_k k'), of dimension 1, while R has dimension 0. Indeed k' tensor_k k' is the localization of k[X,Y] by the nonzero polynomials in X and in Y separately. It is a domain of dimension 1: after inverting k[X] minus zero it is a localization of the PID k(X)[Y], and the diagonal ideal (Y-X) survives since neither multiplicative set meets it. At that diagonal point the dimension of every open neighbourhood is 1. Thus the point dimension changes from 0 to 1. After the first base change the other projection to Spec(k) need not be locally of finite type; 04NS cannot justify the second application.

This is an error in the proof of the source, not a statement dispute: the item is true and is kept exactly. The repaired proof uses the source-fibre comparison behind `more-groupoids.tex` Tags 02YF (parts 1-2), 04LP and `spaces-more-groupoids.tex` Tag 0452. It writes out the pointed comparison directly for algebraic spaces. Each of the two source fibres is a SINGLE base change of R along an embedding K into L. No full restriction U' x_U R x_U U', algebraic closure, or assertion of local finite type after a second base change is used. This correction is below the unit level and changes no chapter/unit proof step. The proof is marked agent-written because it repairs and adapts the source argument rather than reproducing 06FD's faulty intermediate assertion.

## Not duplicates

No new nodes. The existing general scheme result `lem-sc-fibre-dimension-after-base-change` and algebraic-space fibre-product/atlas result `lem-trf-space-fibre-products-etale-covers` are reused. The stronger hypotheses in the existing space-field-extension and geometric-fibre-bound statements prevent substituting them for this item. The item also makes no assertion comparing R with its stabilizer, which is the separate parent node.

## Review by Q68

I read the statements and proofs of Stacks 06FD/06FE in spaces-more-groupoids.tex, the dimension conventions 04N5/04N6 in spaces-properties.tex, the base-change statement and chart proof 04NS in spaces-morphisms.tex, 02FY in morphisms.tex, and the fibre-transport arguments 0452, 02YF and 04LP in the two groupoid source files. There are no new-node sources to review. The route excludes all SGA sources.

Step 1 uses exactly the two cited statements, both opened in full. `lem-trf-space-fibre-products-etale-covers` supplies the algebraic-space fibre product, the surjective etale base change of the chosen scheme atlas and its point-surjectivity clause. The scheme chart pullback V_L is a scheme because this is an ordinary fibre product of schemes over U. `lem-sc-fibre-dimension-after-base-change` explicitly concludes equality of local dimensions of scheme fibres; with bases Spec K and Spec L the fibres are V and V_L. Its local-finite-type hypothesis holds for V to U by the item's chartwise hypothesis on s. No hypothesis on L/K is needed. This gives the dimension equality on charts in the same sense as the item. It is a short direct specialization, so remains an elementary step rather than a new lemma. The quotations in citations.json contain these exact clauses.

Step 2 uses the inline definition of equality of field-valued point classes. The two target classes in Spec K coincide because a field has the single prime zero. Passing the representatives to a common field therefore makes the target MORPHISMS equal. I checked that the two source embeddings K to L are retained separately; falsely identifying them would replace a groupoid on a field by a group over the field. No further field amalgamation theorem is hidden here: the required field extensions are what the stated equivalence relation means.

Step 3 cites the fibre-product node for F_u,F_v and writes out the entire transport. With q=a^{-1} composed with b, q runs from v to u, so right multiplication f composed with q has the stated source and is composable. Right multiplication by q^{-1} is its inverse on every test scheme; associativity, inverse and identity laws show both composites are identities and a maps to b. All formulas commute with pullback and hence define natural transformations, which are exactly algebraic-space morphisms by the definition of the notion. Thus no extra Yoneda assertion or unstated translation theorem is used. Chart dimension is preserved by using the same chart composed with the isomorphism. Step 1 applies to the two source embeddings separately. I checked both the orientation of composition and the chosen lifted points. This explicit few-line computation is elementary; creating a node for it would violate the no-elementary-new-node rule.

Step 4 uses only the defining supremum and the identity arrow. The identity makes R nonempty, so the supremum of its constant set of local dimensions equals that value. The group case is the direct substitution s=t=p and the group operations, with no additional hypotheses.

I checked delivery-errors B through E against the actual node and both cited statements: no new statement-only node to hide a clause, no new duplicate, no unsearched leaf, no citation to a proof in place of its statement, no use of local-ring dimension for neighbourhood dimension, no quasi-separatedness/separatedness/quasi-compactness assumption, and no unproved transport compatibility. All four steps are below 2000 characters. The only off-unit citations are declared as generic tool uses in split_report: scheme base-change dimension and algebraic-space fibre products/etale covers. These do not replace a unit-route argument. The verbatim quotations were copied from the current repository statements.

Edge cases checked: the identity groupoid (including the transcendental-extension counterexample to the source proof), a locally finite type group space, a disjoint union of point arrows from field automorphisms, a positive-dimensional group, and infinitesimal/nonreduced groups such as alpha_p. Source and target may be distinct embeddings, and the source-fibre construction handles this explicitly. R cannot be empty, because e exists and Spec K is nonempty; no finite-type, finite-dimensional, reduced, connected, smooth or decent-space assumption is inserted. All suprema use the stated extended dimension convention.

Mathlib searches were run through msearch.py and their hits read. For the item, the two semantic phrasings returned scheme/standard-smooth and ordinary groupoid facts, not the algebraic-space theorem. The subsequent source-fibre search returned abstract subgroupoid identities, monoid fibre bijections and elliptic-curve base change: none supplies an isomorphism of algebraic spaces or the required dimension assertion. Loogle returned zero hits for both patterns; grep found no AlgebraicSpace/dimension-groupoid declaration. All ten actual searches are recorded with their exact query text, preserving the item's previous searches as history. No service failure was labelled no match.

## Unfinished work

None in the stage-1 split. No Lean was written or compiled. The required server dry run and direct delivery are performed after this review.
