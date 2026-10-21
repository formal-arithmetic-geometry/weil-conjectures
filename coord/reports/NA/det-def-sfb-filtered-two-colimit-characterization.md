## Files written

- dag/nodes/sec-six-functors-basics/det-def-sfb-filtered-two-colimit-characterization.json — statement, split; no exact Mathlib match for the full item. Statement and statement dependencies are unchanged.
- citations.json — verbatim statement excerpts for all cited nodes in each proof step.
- searches.jsonl — msearch's unchanged search log; six searches, all services answered.

No new nodes and no new Mathlib leaves. The unit's key node is sk-def-sfb-filtered-two-colimit, not this characterization, so no unit record is edited.

## Attachments

None. I searched the live lean/WeilConjectures source both for the exact blueprint tag and for FilteredTwoColimit, CategoryCocone, and comparison terminology. WeilConjectures/CategoryTheory/FilteredTwoColimit.lean:63–113 defines the three predicates and their conjunction and proves their projections, but does not construct this coherent comparison functor or prove any of the three iff statements. Its introductory prose is not a declaration proving this item. Specialized constructible and finite-dimensional cocones and StageSystem.cocone_isFilteredTwoColimit do not state this general comparison characterization. The item's lean_audit.slopmaster2 state is none.

## WANTED

None. All used sources are present locally. No SGA source is used.

## Corrections and limitations

No statement dispute or mathematical source error was found. The imported proof had no dependency citations, elementary was null throughout, and the final categorical criterion was uncited. The split now cites the model and the precise conditions, the existing filtered-set-colimit leaf, and two existing equivalence leaves. In particular the existing equivalence-construction node states only the sufficient direction; I did not incorrectly use it for the converse, which instead cites the existing quasi-inverse Hom-bijection node. No proof argument is exported to a new node.

The complete source is main-20261015, sk-def-sfb-filtered-two-colimit/det-def-sfb-filtered-two-colimit-characterization.md and its .proof.md, together with the chapter and unit records. The model's coherent normalization is an additional hypothesis of this characterization and is not asserted for arbitrary CategoryCocone data. The unit's second proof paragraph supplies exactly this route. The current sk-def-sfb-filtered-two-colimit node already makes that distinction explicit.

Blueprint and DAG searches for filtered 2-colimit, the item id, the generic equivalence criterion and Hom-set bijections found the existing model, conditions and generic tools. No other blueprint statement is the same as this three-part characterization; blueprint.same_as is []. Mathlib searches were run through msearch: leanfinder in two distinct phrasings, loogle for IsEquivalence, leansearch for finite-stage equality, and two grep patterns restricted to CategoryTheory. I read the returned hits: the set-colimit injectivity results address the set-level subargument, IsEquivalence and asEquivalence address the last criterion, and prestack-descent comparisons and monad/comonad comparisons are different constructions. The whole item is not a one-line specialization of those hits.

## Review by NA

I read delivery-errors B–E in full and checked this split against its specific failure modes. This is my own review as the direct-delivery author, not a claim of independent review.

For the item I read the current blueprint statement and all three numbered proof arguments plus its final sentence. The statement is preserved byte for byte: the hypotheses remain directed I and a coherent normalized cocone, and all three iff clauses and the equivalence conclusion remain. There are no new nodes for which a standalone statement, source, duplicate check, or edge-case repair is needed. The imported flags and all blueprint fields are preserved except filling same_as.

Step 1 cites the model's objects-as-pairs and its object map, and the conditions node's (Obj) clause. Those statements really identify the two essential-surjectivity predicates; reversing the object isomorphism is elementary.

Step 2 cites the model's Hom diagram and displayed comparison map and clause (1) of lem-weil-pbc-filtered-colimit-sets-elementwise for representatives. I verified the index hypothesis explicitly: the common-stage tail is a subset of the set I, directed and nonempty for fixed i,j, and is a thin category, so the existing small-filtered-category lemma applies. The formula for the image of [k,g] is exactly the formula in (Hom-surj). The two fullness implications are direct unpacking, not a hidden descent theorem.

Step 3 uses (Hom-inj) only in the exact form stated in the conditions node, applied to u,v between T_im x and T_jm y in C_m. The model states the transition formula and that the comparison is well defined, so passing to m preserves its images. I wrote out cancellation of the theta maps and the tau conjugation at n, rather than treating transition t_mn as the bare T_mn. Clause (3) of the set-colimit leaf converts equality there into equality of classes. It is a short elementary representative calculation after those cited inputs.

Step 4 uses faithfulness to identify the normalized classes at k, then clause (3) of the same set-colimit leaf to obtain one later stage. The model explicitly assumes T_kk = Id, theta_kk = id and tau_kkn = id; this is why the final equality is T_kn(g)=T_kn(g'), precisely (Hom-inj). No strictness of arbitrary transitions is assumed.

Step 5 cites lem-trf-fully-faithful-ess-surj-equivalence for the sufficient direction only. I read its full statement, including its universe convention. Both categories can be placed in a common larger universe; the Hom-colimit index remains the small tail already checked. For the converse I read the statement of lem-sf-quasi-inverse-hom-bijection: it gives bijective Hom maps from a quasi-inverse and two natural isomorphisms, without presupposing triangle identities. The counit gives essential surjectivity directly. Thus neither equivalence criterion is being used beyond its actual statement. These are existing Mathlib leaves, so no off-route unproved theorem is substituted for the unit route.

I also read the sources of the three generic tools: Stacks categories.tex, Tag 04AX / section-directed-colimits (eventual equality of elements) and Tag 02C3 / lemma-equivalence-categories and preceding definition-equivalence-categories. In Mathlib I checked Limits/Types/Filtered.lean:141–160, Equivalence.lean:349–354, :550–552, :606–609 and :642–649, and Functor/FullyFaithful.lean:173–175. They agree with the cited nodes' recorded Mathlib matches. There is no uncited construction of a quasi-inverse in this split.

For small cases I checked a singleton I (the three clauses become ordinary essential surjectivity, surjectivity and injectivity of the sole functor), empty stage categories (the Hom clauses are vacuous and Obj forces the target empty), and a constant identity diagram. The forward injectivity argument also allows a nonfaithful stage functor whose distinct arrows become equal only at a later stage: it uses exactly eventual equality, not injectivity at the original stage. No finiteness, additive structure, abelian hypothesis, or universe restriction beyond ordinary categories was introduced. Every step has fewer than 2000 characters. All citation quotes are copied from the statements, not their proofs. The proof dependencies are exactly the union of the step uses. Nothing is left unfinished mathematically.

## Validation

The required deliver.py --no-push server preflight passed on 2026-10-21 (initial dry-run commit 4cabe134fdc). It reported OK (not pushed), after running the server checks. The final report is then revalidated before pushing. No Lean file was written and no compiler or Lake command was run.
