# Stage-1 report: lem-trf-initial-henselian-colimit-comparison

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-initial-henselian-colimit-comparison.json`: item, statement unchanged, split into five steps; no Mathlib match for the entire statement.
- `citations.json`: one entry per step/node citation, quoting the cited statement verbatim.
- `searches.jsonl`: actual msearch.py results for this item. The item's inherited Q20 searches remain intact, and the Q82 searches are appended to its mathlib_searches.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches under `lean/WeilConjectures/` for the exact blueprint tag and henselization/initial/colimit terminology found no declaration covering this item. The existing `Algebra.map_into_henselian_colimit` is the lifting theorem used as a dependency, not this comparison and cocone-transfer statement. `Algebra.henselization_universal_property` concerns a specified etale-neighbourhood colimit of a henselian pair; `pairHenselization_colimit` concerns pair henselizations in a directed system. Neither states the present item under its hypotheses.

## WANTED

None. The relevant Stacks sources and current blueprint are available locally.

## Corrections and completion

No statement dispute or change. The imported item had no proof; the sandbox contained only dispatcher brief markers, no previous node, report, searches, or delivery artifacts. There was no running deliver.py process for this item before work resumed. The copy preserves its source, historical blueprint chain, created metadata, and inherited searches. The proof now avoids assuming either a residue-field isomorphism for H or an etale-colimit presentation of H. Nothing is left unfinished in the split.

The current main-20261015 blueprint ancestor `lem-trf-local-term-locality` uses the contracting-correspondence argument. As the parent `lem-trf-henselization-prime-ind-etale` and this item's existing blueprint.from record explicitly say, this is a historical commutative-algebra auxiliary below that ancestor, formerly the parent's steps 4–6. No unit, ancestor statement, or contracting-correspondence route is altered. This item is not the key statement of sk-i-curve-zero; no unit realization fields are edited.

## Not duplicates

No new node is proposed. DAG searches for Tag 08HR and henselian/initial/colimit terminology, and whole-blueprint searches for henselian, henselization, henselian local, initial and colimit, were read before writing. Reuse `lem-weil-pbc-map-into-henselian-colimit` rather than creating another lifting lemma. `lem-sc-strict-henselization-comparison` instead compares two specified strict-henselization triple colimits over a separable closure. `lem-per-pointed-etale-limit-henselization` requires a particular directed pointed-etale presentation and additionally proves congruence/completion assertions. Neither duplicates the present initial-property comparison with no presentation assumed for H.

## Review by Q82

I read Stacks algebra.tex Tag 08HR, label lemma-map-into-henselian-colimit, including its proof by stagewise maps supplied by lemma-map-into-henselian. I read categories.tex Tag 002F, label definition-colimit, including both the transition-map equation and uniqueness of the mediator. I verified the tag-label mapping in stacks-project/tags/tags, including Tag 097I for the ind-etale definition. I read the complete statements of all three cited nodes: `lem-weil-pbc-map-into-henselian-colimit`, `def-weil-pbc-ind-etale-algebra`, and `def-weil-pbc-category-colimit`. There are no new nodes requiring additional sources.

Step 1 uses the ind-etale definition only to obtain a filtered presentation by etale R-algebras. The lifting node explicitly gives existence and uniqueness for an R-algebra map with prescribed maximal-ideal preimage and prescribed compatible residue map. Here q=m_C is prime, its preimage and the preimage of m_T both equal m by the two local structural maps, and tau=e_T e_C^{-1} is compatible because tau e_C=e_T. At the maximal ideal of a local ring its residue field is the quotient by that ideal: localization changes no elements, because every element outside the maximal ideal is already a unit. A local map induces the residue map by sending the class of c to the class of its image. Since e_C is onto, every local R-map has precisely this residue map. Thus the cited uniqueness really applies to every local R-map. No bijectivity of e_T (in particular e_H) is used. This is the only non-elementary step, and it cites the full lifting theorem, not its proof or a henselian definition.

Step 2 is the elementary uniqueness argument with two initial local-map properties, one proved in Step 1 and one assumed for H. C itself is henselian by hypothesis, so it is an allowed target for both properties. I checked both composites over R and both local conditions before comparing gf to id_C and fg to id_H. Neither uniqueness assertion presupposes that H is ind-etale. No extra node merely restating this clause is introduced.

Step 3 uses exactly the universal mediator and uniqueness given by the category-colimit definition. The transported maps are mu_i=f lambda_i; for each transition d_ij their equation is mu_j d_ij=mu_i. Given a cocone t_i with any ring vertex B, descend it to u:C->B and use v=u g. The equalities v mu_i=t_i and wf=u imply w=wfg=ug, proving existence and uniqueness at H. This is a direct universal-property computation, rather than an unproved invocation of transport.

Step 4 uses the same definition for its explicit nonempty-index clause: a filtered category has an object i. The hypothesis that the original ring cocone induces the specified P-structure means lambda_i s_i=rho_C for every i. Since f and g commute with R, they commute with the composites from P. For any P-algebra cocone to B, the equation u rho_C=u lambda_i s_i=t_i s_i=rho_B proves the mediator is P-linear; its composite ug is P-linear as well. Ring uniqueness then gives algebra uniqueness. No theorem asserting preservation of colimits by a forgetful functor is being silently used.

Step 5 uses precisely the ind-etale definition: the same small filtered diagram now has H as its P-algebra colimit and each stage is etale of finite presentation over P. The specified structural map is retained by f eta_C=eta_H. The finite-presentation and etale notions in the unchanged statement retain their original definition dependencies.

I checked delivery-errors B–E against the files: no new statement-only nodes, inline proof sketches, or unsupported notions were added; existing statement dependencies remain relevant. TeX has single backslashes after JSON decoding. Every cited theorem says the clause used, with the prime, residue, henselian and size hypotheses verified above. Every non-elementary fact is cited; the remaining steps are written universal-property calculations. There is no new node disguising a clause of the item. No proof dependency points back to this item. Each step is shorter than 2000 characters; the full five-step proof is 2800 characters. The off-unit lifting theorem is explicitly declared as a generic tool in split_report.tool_uses, because sk-i-curve-zero provides no commutative-algebra substitute.

For small cases I checked R=C=H a field, giving identity maps and ordinary cocone transport, and R already henselian with C=R. For arbitrary non-Noetherian R none of the steps invokes finiteness of R, its ideals, or H. A one-object filtered diagram gives ordinary transport of an isomorphism; the empty category is excluded by filteredness and is exactly why Step 4 can choose an index. Arbitrary P, including a P-structure with kernel, works because the calculation uses its ring maps only. Zero rings as diagram stages cause no change to the universal-property argument (when the stated cocone exists). The local rings themselves have maximal ideals, so the degenerate zero ring is not an omitted local-ring case.

The Q82 Mathlib searches actually run were leanfinder with two phrasings, LeanSearch, Loogle on HenselianLocalRing, and two greps in RingTheory and RingTheory/Etale. All services returned results. I read Henselian.lean around HenselianLocalRing and TFAE (root lifting only), and StandardEtale.lean around hom_ext, homEquiv and the square-zero lifting lemma. Those supply neither an ind-etale-to-henselian comparison nor its full arbitrary-P cocone assertion. The generic elementary calculations in Steps 2–5 are kept as steps; making them extra nodes would violate the elementary-node rule.
