## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-coherent-cocone-normalization.json`: statement node, now split into ten explicit elementary steps; no exact Mathlib match. Its statement, statement dependencies, inherited search records, and blueprint provenance are retained.
- No new nodes and no Mathlib leaves.
- `citations.json` records a verbatim statement quotation for every step/node citation. `searches.jsonl` is the unedited search-command log. `write_split.py` is sandbox-only preparation material.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id and for normalization/normalisation with cocone, and searched the StageSystem and colimit files for the notions. Read `CategoryTheory/StageSystem/Basic.lean` and `StageSystem/Const.lean`: they give stage systems, coherent cocone descent and a colimit property for stage inclusions, but no declaration stating this diagonal-normalization construction with all three invariance clauses. In particular `Morphism.ofCocone` and `cocone_isFilteredTwoColimit` do not prove this item. No sorry declaration was treated as a completed attachment.

## Literature wanted

None. This is an explicitly agent-formulated auxiliary calculation, not a theorem falsely attributed to a missing external source. No SGA source is used.

## Faults and changes

The item had no proof. Its source correctly says that it formulates an auxiliary normalization lemma, without claiming the blueprint already proves it. I read the main-20261015 model and conditions markdown statements, and the qbar statement and proof. The original statement is well typed with its stated convention suppressing functor associators/unitors and is unchanged. No STATEMENT-DISPUTED issue was found.

I supplied all coherence calculations explicitly rather than invoking an unnamed transport or strictification theorem. In particular the right repeated-index unit requires naturality of epsilon, the pentagon requires naturality of beta and tau, and the cocone equation requires naturality of theta. Hom-inj is checked on the original stage morphisms, as its definition actually requires; it is not confused with equality of arbitrary representatives of different stages.

The chapter and unit records were read. This auxiliary node supplies the normalized model used by the scalar-extension pair-category argument under the qbar theorem's final independence sentence; it changes neither the unit nor chapter route. Its cross-unit proof citations are definitions specifying the data and conditions, not substitute theorem routes. No tool-use authorization is needed.

## Searches and duplicates

Before considering extra nodes I searched the whole DAG for unital coherent cocones and cocone normalization, and the whole imported blueprint with `tools/blueprint_refs.py search 'coherent cocone normalization'` and `search 'unital cocone'` (zero matches). `ancestor` confirmed `thm-weil-pbc-qbar`. The existing filtered-two-colimit cocone/model/conditions nodes already state exactly the definitions needed. No auxiliary lemma remains after writing out the elementary equations, so no new node and no potential duplicate pair was created.

Ran the required msearch command for LeanFinder, Loogle, grep and LeanSearch, with a second LeanFinder phrasing about transport of composition and identity comparisons. The results are logged as returned and recorded with their exact query strings. Loogle returned zero hits. LeanSearch and LeanFinder returned cocone category structures, free-bicategory normalization, pseudofunctor constructors, Grothendieck constructions, and comparison-isomorphism formulas. I read the candidate source in Mathlib's `CategoryTheory/Bicategory/Coherence.lean`, `Functor/Pseudofunctor.lean`, `Functor/LocallyDiscrete.lean`, `Grothendieck.lean`, and `Functor/Cat/ObjectProperty.lean`: free-bicategory normalization changes the free bicategory, the constructors require coherence rather than proving this normalization, Grothendieck mapCompIso concerns composition of transformations, and ObjectProperty.mapComp restricts an existing pseudofunctor. None specializes in one line to this item's diagonal replacement and the preservation of Obj, Hom-surj, and Hom-inj. All services answered; none was recorded as unavailable.

## Not duplicates

No new nodes, hence no new/existing pairs. The item is not a restatement of the model definition: it starts from nonidentity diagonal transitions and proves that replacing them preserves the original cocone's three properties.

## Review by NA

I read the current model source at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-filtered-two-colimit/det-def-sfb-filtered-two-colimit-model.md`, the adjacent cocone and conditions definitions, their actual DAG statements, and the ancestor qbar statement/proof. The size-convention statement was also read: the construction adds no categories, colimits, or choices outside the fixed universes. There are no new nodes to compare against an external source. The proof is marked agent-origin because the source specifies the normalized model without proving this auxiliary construction.

Step 1 uses the cocone definition's exact list of transitions, vertex functors and natural isomorphisms. It deliberately takes no coherence result from that definition, which explicitly imposes none. Step 2 introduces B and tau-prime with matching source and target and explains their naturality from the naturality squares of the given transformations. These are componentwise elementary constructions, not a cited transport theorem.

Steps 3 and 4 check both pentagon composites after postcomposition with the same invertible beta_il. For step 3 the naturality square is beta_kl evaluated on tau-prime_ijk. For step 4 it is tau_jkl evaluated on beta_ij. Both final composites have the identical displayed B_ijkl on their right, so the given original pentagon and cancellation prove the desired equality. I checked the domain is T-prime_kl T-prime_jk T-prime_ij and codomain T_il throughout. No generalized coherence theorem is being imported without a node.

Step 5 substitutes tau_iij = T_ij epsilon_i and cancels T_ij epsilon_i against its inverse. Step 6 instead uses the explicitly written naturality equation of epsilon_j on beta_ij before cancellation; simply cancelling without this square would be wrong. These steps prove both repeated-index cases even when i=j, so they do not hide a distinct-index hypothesis or a missing all-equal case.

Step 7 substitutes the transported comparisons, uses the given cocone identity, and writes the naturality square of theta_jk on beta_ij into the equality chain. The diagonal theta identity follows from the given theta_ii = Phi_i(epsilon_i). Its single cited model node is used only for the three explicitly stated normalization/cocycle/compatibility hypotheses. Its later assertion about constructing a category is not used, avoiding a dependency on its proof or an unnecessarily strong result.

Step 8 explicitly writes the arrow bijection and its inverse, and the unchanged-image equation follows by functoriality and cancellation. Step 9 cites the actual conditions statement: Obj refers only to the unchanged Phi_i and D, while Hom-surj quantifies over a common stage and its image formula. Keeping that same stage and using the two directions of the bijection proves the equivalence. Step 10 cites the Hom-inj clause, whose input is two morphisms already in C_k with equal Phi_k images. Naturality of beta_kl gives conjugate images under T_kl and T-prime_kl, so the very same witness l works in both directions. Each citation in these steps has a verbatim quotation in citations.json, and proof_deps is exactly the union of uses.

I checked the small cases of an empty indexing poset (if directedness is defined vacuously), a singleton poset, terminal/empty stage categories, equal source and target stages, common stage k=i or k=j, the fully repeated-index triple, and a nontrivial unit automorphism of the identity functor. The empty case makes every construction indexed by I vacuous and preserves whichever truth value Obj has. In the singleton case normalization produces identity transitions; the unit naturality calculation still works for nontrivial epsilon, and Hom-inj at that sole stage is equivalent by conjugation, not by falsely assuming a transition was initially identity. Directedness and smallness are already hypotheses and no maximum, strict successor, nonempty stage, or faithfulness is assumed. Every functor/isomorphism used in a cancellation is among the given or constructed data. The equations are valid componentwise, so no extra small-colimit existence theorem is needed.

Against B--E: no new statement-only nodes, new notions, unsearched leaves, SGA references, or source tags arise; no source theorem is attributed to a definition; no clause was moved into a new node; no circular dependency was introduced; and every transport asserted has its actual equation in the item. All ten steps are elementary applications of the given naturality, functoriality, inverse and coherence identities, with lengths below 2000 characters. There was no previous delivery or return to repair and no second worker is claimed.

## Unfinished work

None in this stage-1 split. The maintainer's independent review remains part of the normal delivery process.
