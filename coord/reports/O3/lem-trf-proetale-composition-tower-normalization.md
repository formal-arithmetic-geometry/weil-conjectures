## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proetale-composition-tower-normalization.json`: repaired split, eight steps; no new nodes, no Mathlib leaves.
- `citations.json`: one verbatim statement quote for every node used in every step. Full statements are quoted so the hypotheses remain visible.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item tag, pro-etale composition/tower normalization, proper/open interchange, and `lowerShriekComp` found no project declaration proving this statement. The `TraceFormula/Defs.lean` composition fields are supplied six-functor structure data, not a declaration computing the finite-constant-ring compactification compositor on arbitrary-field etale-origin inputs. The upstream master remains reference material, not evidence of a closed proof.

## WANTED

None.

## What was wrong and what changed

This repairs the returned delivery, not just its base commit. I compared the retained node with the current shared node: before repair their differences were `proof`, `proof_deps`, `proof_origin`, `split_report`, and `status`. The statement, source, ancestry, item-owned search results, and other metadata agree and are retained. The initial required dry run of that retained work exited successfully, at `c3787195d9`; that mechanical success does not fix the mathematical return.

E1/C4: both old tower citations assume the finite-field geometric coefficient conventions. I removed them from all proof steps and from the declared tool uses. The replacement is an explicit computation of the construction, using the existing general-Noetherian-scheme site clause of `lem-sp-proper-open-coefficient-mate`, the exact-exchange identification `lem-weil-pbc-transport-identifies-exchange`, and the named etale proper/open representative. No finite-field descent assumption enters. The item and its general-field citer are unchanged.

C3: no proof paragraph of the old normalization node is used as a theorem. Step 7 performs the actual construction with the supplied candidates, including the inverse open-restriction exchange and both named compositors. Step 8 computes both specializations defining chi and cites the identity direct-image and identity-square/open-adjunction facts. The final compositor's normalization is constructed by its Hom bijections and the unit-preserving conjugate-isomorphism statement in Step 6.

E3: the old inference from invertibility of lambda to invertibility of its adjunct has been removed. Step 5 uses adjunction solely for equality. Step 8 identifies gamma with chi, a composite of the two canonical alpha isomorphisms on the stated models; those isomorphisms prove invertibility. Lambda's own invertibility is proved separately by the proper-base-change theorem and the open unit.

The pre-existing searches are preserved and their recorded results were read: the semantic hits concern compact support of functions or sheaf pushforward composition, the grep hits are site/ell-adic definitions, and the Loogle hits are general mate calculus. None states the specified pro-etale compactification composition formula. No new Mathlib claim or new search is recorded. Whole-DAG and whole-blueprint proper/open and composition searches were reused to locate existing tools, so no new lemma or clause node was necessary.

## Unfinished work

None within this split. Existing cited statements retain their own downstream proof obligations. Only stage 1 was performed: no Lean writes, compiles, Lake, direct repository writes, or agents.

## Not duplicates

No new nodes. In particular, the repair does not create a general-field restatement of either old tower node or move a clause of the item into a new node.

## Review by N3

I read the returned item, all statements cited in the repaired eight steps, the general-field citer `lem-trf-proper-composition-site-transport`, the `sk-d-weil-push` unit and trace-formula chapter, and the current blueprint's `lem-trf-weil-shriek-operator-fibres` proof, especially (beta). For the construction I read the entire main-20261015 `thm-sf-comp-composition.proof.md`, including its displayed proper/open arrow and the following composition sentence. I also read `more-etale.tex`, Tag 0F7B (`lemma-shriek-proper-and-open`), its K-injective construction, and Tag 0F7J (`lemma-shriek-composition`), its four-line computation. These sources determine the candidate route. The explicit coefficient/site naturality and named-exchange equalities are taken from the statements of the existing agent-stated tool nodes, rather than attributed verbatim to Stacks. No SGA source is used.

Step 1 uses the compatible-triangle statement literally for b open, r proper, bj=a, rj=h, and the Cartesian square pb=ir, with the variable renaming written out. The coefficient definition states finiteness of Lambda. Finite-type-over-Noetherian and the definition of properness give Noetherian schemes for the compactifications; the open-subscheme statement gives it for H. The locally-Noetherian and qcqs-permanence statements then give exactly the qcqs hypotheses needed for p and r in Step 4. A field being Noetherian is the elementary two-ideal argument. Thus the replacement site clause has its actual Noetherian hypotheses for every field in the item, including characteristic zero and fields not algebraic over a finite field.

Step 2 uses the exactness statements for comparison and both open extensions, and the canonical open-extension comparison, to give the explicit witness j_!^e L for J_j M. It also gives b_!^e K for J_b N, so the proper-base-change application later has a witnessed input. The etale-origin definition supplies exactly these triples, with the witness carried along; merely belonging to an unspecified full subcategory is not substituted for a witness.

Step 3 reads the site clause of `lem-sp-proper-open-coefficient-mate` at the square (b,r,p,i) and the identity finite-ring map Lambda to Lambda. Its displayed equation is solved for the named pro-etale map T, using exactly its e and d isomorphisms. The separate direct-image comparison statement supplies the canonical counit normalization and invertibility of d. The open-extension comparison supplies e. The K-injective representative is explicitly part of the statement of `lem-cbc-proper-open-interchange-coherence`, and agrees with the map specified in the coefficient-mate statement. These tools have no finite-field hypothesis and no finite-cohomological-dimension hypothesis.

Step 4 checks the exchange with the actual statement equation of `lem-weil-pbc-transport-identifies-exchange`, with f=p, f'=r, g=i, g'=b. It does not confuse the unbounded etale exchange or another ringed exchange with the item's Ex^p. The unit-normalization statement for b matches the two specified open units. Exactness descends this sheaf equation termwise. The finite-level pro-etale proper-base-change statement applies because p is proper, Lambda is finite, and J_b N has the Step 2 bounded-below etale witness. The derived open-adjunction statement says that eta_b is an isomorphism. These are precisely the two factors giving lambda's invertibility.

Step 5 uses the open-adjunction prescription stated in the coefficient-mate site clause, now with the exact exchange and unit from Step 4. The derived Hom bijection supplies its transpose and uniqueness. This is a two-line equality argument, marked elementary. In particular it contains no assertion that the adjunct of an isomorphism is invertible.

Step 6 checks the finite-level clause and direction of the direct-image compositor: the cited statement is c from P_qp to P_q P_p, so the item's D is its inverse. For E, the derived open adjunctions identify the two Hom sets with Hom(M,a^*F). The conjugate-isomorphism unit-equation statement gives exactly the canonical comparison preserving that restriction and its unit. Its uniqueness fixes the identity-open normalization. This verifies the item's normalization without using the weaker sheaf-adjunction statement for a derived composition assertion.

Step 7 expands the source construction itself. Over V its displayed map is inverse proper base change with the open units, so the computed transpose is lambda inverse; the open Hom bijection identifies that map with T. The chosen etale representative and the site clause verify the same named-map normalization under site comparison. Applying P_q and the Step 6 compositors gives the two arrows in the item, and Step 5 substitutes gamma. The composition theorem is cited for preservation and existence of the canonical composition isomorphisms; no tower formula is claimed to occur in its statement. No part of the argument cites the proof of another DAG node.

Step 8 is the explicit short specialization of this computation to (r,i) and (b,p). For the first pair the compactifications are (i,id) and (b,p); its residual open is id_H. For the second they are (id,p) and (b,id); its interchange square is an identity square. The direct-image identity clause, identity-square open comparison, ambient unit-square-counit definition, and open triangle identities justify removal of the identity factors. Thus alpha_i,r=T while alpha_p,b is identity on P_p J_b; chi=T=gamma. The actual composition theorem states that these alpha maps are isomorphisms on the witnessed category, so this proves invertibility for the correct reason. Proper coincidence throughout uses the literal identity-open candidates of the candidate definition.

I rechecked B through E against these statements. There are no new statements needing B1-B9 tests and no new clause or duplicate nodes (D1-D2). Every non-elementary operation used is a statement citation, including coefficient/site transport, exactness, witness preservation, and the compositors; every citation in `citations.json` is verbatim. Off-unit uses are declared as generic tools with their role; the two rejected finite-field tool declarations are gone. The proof follows the same unit route and no target statement or definition changes. Every step is shorter than 2000 characters, and the explicit candidate computations introduce no hidden lemma with different hypotheses.

For small cases, with i=b=id, lambda, T and gamma become the identity on P_p=P_r by the adjunction units; the final formula is ordinary direct-image composition. With p=r=id, they are the identity on J_i=J_b and the formula is open-extension composition. For h=id or f=id with their identity compactifications, the identity-square and identity-compositor clauses give the identity composition map. For empty U the witnessed input and all displayed candidate values are zero. Properness of p and r is supplied by compactifications and base change, never by assuming h or f proper. These checks also separate the valid final isomorphism argument from the false general principle about adjuncts: a nontrivial open counit can still fail to be invertible on arbitrary ambient inputs.
