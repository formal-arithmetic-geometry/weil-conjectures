# Q27: lem-pur-comparison-global-resolution-model

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-comparison-global-resolution-model.json: existing statement node, now split into seven proof steps. Statement and statement dependencies unchanged. No new nodes and no new Mathlib leaves.
- citations.json: a literal statement excerpt for every node citation of every numbered proof step.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and item id, comparison/resolution notions, derived units and cocycle comparisons. The general derived-adjunction machinery does not state all the item's site-specific clauses. No attachment is asserted on the strength of a sorry declaration.

## WANTED

None. The blueprint and supporting Stacks sources are available locally.

## Corrections and findings

The item was an unsplit, agent-stated refinement of the opening paragraph of the current main-20261015 proof of prop-pur-gm-relative-kummer. That paragraph authorizes transport of global classes but does not itself give this chain formula. The proof is therefore marked agent-written, with the blueprint place and supporting Stacks tags specified. No disputed statement, changed hypothesis, or route replacement was needed. The item is not its unit's key statement, so no unit realization fields were changed.

The existing general bounded-below resolution-existence statement alone would not justify the requested nonnegative bound. Reused lem-weil-pbc-complex-injective-resolution-mono instead: its statement explicitly retains every lower bound a, so a=0 is legitimate twice. Also reused lem-pur-comparison-unit-injective-model, which already states the exact derived-unit representative with an arbitrary replacement of the inverse image. It would be a duplicate to introduce another such lemma.

The imported Mathlib search records were retained. The five additional searches in searches.jsonl were run through msearch.py and their actual successful results appended to mathlib_searches. Two different LeanFinder phrasings returned sheaf adjunction/construction declarations and ordinary resolution formulas; LeanSearch and Loogle returned general derived adjunction units. Read Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean, especially derivedη_fac_app and derived, and the project's PlusAdjunction.lean normalization interface. These are ingredients rather than a one-line specialization proving the whole item. No new Mathlib leaf is claimed.

## Not duplicates

No new node was created. The near neighbour lem-pur-comparison-unit-injective-model concerns a derived unit before global sections, for an arbitrary bounded-below source complex. The present item adds existence of nonnegative resolutions, fixes both augmentations and their target identification, evaluates the final-object comparison, and calculates the cohomology classes. It cites that neighbour rather than restating it as a new prerequisite. The searches of the whole imported blueprint for comparison unit, global cohomology comparison, normalized global, injective-resolution representative and terminal section found no blueprint node stating the whole present item. The existing ancestor is prop-pur-gm-relative-kummer through lem-pur-site-comparison-edge-section; that link and its precise opening-paragraph place are retained.

## Unfinished work

None for this one-level stage-1 split. Existing cited nodes retain their own statuses and are not being claimed as finished Lean proofs.

## Review by Q27

I read the current blueprint proof's opening paragraph, its Kummer/base-change route, the chapter and unit records, SETUP's three levels and GOAL.md. The split serves exactly the transport of classes from the small etale to the small pro-etale site; it uses no exceptional inverse image or SGA source. I read Stacks derived.tex Tag 013K (lemma-injective-resolutions-exist, especially part (3)), 070J (lemma-bounded-below-injectives-K-injective), 070Y (lemma-K-injective-defined), 0DVC (lemma-pre-derived-adjoint-functors) and 09T5 (lemma-derived-adjoint-functors); injectives.tex 079H (theorem-injective-embedding-grothendieck) and 079Q (remark-existence-D); homology.tex 015Z (lemma-adjoint-preserve-injectives); proetale.tex 099R (section-comparison) and 099W (lemma-compare-cohomology); and sites-modules.tex 04JC (lemma-flat-pullback-exact). The proof is an explicit agent refinement of these inputs, not a claim that 099W alone states a normalized chain representative.

For step 1 I opened the statements of the ring-sheaves Grothendieck theorem, Grothendieck enough-injectives theorem, same-bound complex resolution lemma, comparison-pullback exactness lemma and bounded-below-injective K-injectivity lemma. They give precisely the two nonnegative complexes and quasi-isomorphisms. The small-site universe hypothesis is supplied in the item, the coefficient sheaves are actual ring sheaves, and a=0 is allowed; no finiteness or noetherian condition on U is added. For step 2 I checked that the exactness node explicitly preserves quasi-isomorphisms, so the composite augmentation beta is an isomorphism after localization for every permitted pair.

For step 3 I read the comparison-morphism node's restriction formula and the termwise-adjunction node's clauses on complexes and its explicit transpose formula. Those state what is needed to construct the chain map h, not just an abstract derived Hom bijection. Evaluation at U preserves the differential and coefficient action literally. For step 4 the adjoint-preserves-injectives statement applies to N_U as the right adjoint of exact A_U. The right-derived-plus-injective statement explicitly includes its natural comparison and computation on every bounded-below termwise injective complex, so it applies to I, J and N_UJ. Left exactness of section evaluation and N_U is justified by the kernel formula in the step. No preservation of injectives by A_U is assumed.

For step 5 I opened lem-pur-comparison-unit-injective-model and used its displayed equality with M=I and j=t. Its finite commutative ring, boundedness, exact-pullback and injective-target assumptions all hold here. I wrote the naturality equation at rho=Qi explicitly, obtaining RN_U(beta) eta_F = alpha_J Qh rho. This checks that the target identification is the one induced by t A_U(i), which is essential for an arbitrary t. It does not borrow an unstated calculation from the proof of another node.

For step 6 I checked the statements of derived-sections-pushforward and comparison-global-cohomology: the former specifies the natural comparison induced by terminal evaluation, and the latter specifies global comparison as derived unit followed by that comparison. With the computing complexes in step 4, this terminal evaluation is degreewise the identity. Naturality of the right-derived comparison then makes the actual composite Qw. For step 7 the cocycle and boundary equalities are written out. The section formula follows from the unit in the stated colimit/sheafification construction at the pair (U,id), with the canonical constant-ring identification from comparison-pullback exactness. It is not an uncited assertion about preservation of injectives or an arbitrary transport of cohomology classes.

I tested F=0, the empty scheme and q=0: zero section complexes cause no exception, and the q=0 argument uses no nonexistent negative boundary. I also checked the normalization test t replaced by -t: w and beta both change sign, so the resulting cohomology comparison under the specified target identification is unchanged. This is why the proof carries beta through the naturality equation rather than declaring QJ equal to A_UF by an unspecified isomorphism. Noninjectivity of A_UI causes no problem, because it is replaced by J before deriving N_U or pro-etale sections.

Against delivery-errors B--E, there are no new unsplit statements, elementary nodes, duplicate nodes or new Mathlib claims. All statement dependencies were retained, all proof uses are existing nodes and are supported by literal excerpts in citations.json, and proof_deps is exactly their union. Definitions are used for their stated formulas only. The potentially non-elementary resolution, derived-unit and derived-computation steps are marked non-elementary and cite theorem nodes. The remaining elementary steps are localization/composition and the explicit cycle/unit calculation. Every step is below 2000 characters, and none conceals a separate comparison lemma. Off-unit statements are declared as generic tools in split_report.tool_uses; they supply homological-algebra/comparison infrastructure, not a replacement of the Kummer unit route. No repository, launcher or Lean source file was changed and no compiler was run.
