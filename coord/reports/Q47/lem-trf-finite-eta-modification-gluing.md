## Worker report

Q47, 2026-10-18. Item: lem-trf-finite-eta-modification-gluing. Stage 1 only. The original sandbox contained no item, report or search log. I continued from the current shared item, preserving its statement, source, ancestry, original searches and creation metadata. I wrote no Lean, ran no compiler, and changed no shared file.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-eta-modification-gluing.json: statement, now split into thirteen proof steps, using thirty existing dependencies; not a Mathlib leaf.
- citations.json: one entry per step/dependency incidence, quoting the dependency's verbatim statement. Full statements are retained so that the hypotheses of each quoted fact remain visible.
- report.md: this report and author's review.
- searches.jsonl: actual msearch.py output records. write_split.py is sandbox-only preparation code, not part of the DAG delivery.

## New nodes

None. In particular I did not create a pairwise-comparison node restating a clause of the item, a graph lemma already supplied by the scheme-image interfaces, or another normalization/limit theorem. There are zero new Mathlib leaves.

## Attachments

None for this item. Searches of WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the blueprint tag, eta-modification, Temkin, reduced-fibre terminology and finite gluing found no project declaration stating this result. The returned normalization, reduced-fibre preservation, and graph-image declarations only cover ingredients. The upstream master source was searched read-only too; it was not used as proof evidence. Existing closed dependencies, including lemma-nagata-scheme-image-partial-section and the relative-Spec interface, are cited by their existing node ids, not reattached under new ids.

## WANTED

WANTED: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, Corollary 3.5.4 and Theorem 3.5.5 Step 1, printed pp. 21–22, for lem-trf-finite-eta-modification-gluing. The archival path in the existing node does not exist in this checkout. I read the primary PDF online at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf (arXiv:0707.3953v3, PDF pages 21–22), without downloading into the repository. Accordingly proof_origin.by is agent, with the online outline completed using the local Stacks sources listed below.

## What needed repair or clarification

The item statement is unchanged, including both schematic-density clauses. The empty proof needed all of the comparison and descent argument. A generic isomorphism alone is not silently treated as an eta-modification: step 3 first spreads its inverse and both inverse equations to a common affine base open, and step 4 proves schematic density from flatness. Step 8 checks the common graph's dense isomorphism open before applying eta-normality.

Only the normalization N of S is assumed normal. The theorem on geometrically reduced flat families is applied to the two source models over N, never to the possibly non-geometrically-reduced target H. The two projections of their common graph are then the finite modifications to which eta-normality applies. This spells out the comparison compressed in Corollary 3.5.4.

The finite subalgebras in Properties 0817(1), rather than the abstract finite-and-finitely-presented approximants of 0817(2)/09YZ, are essential: their embedding in the generic field ensures the chosen T_lambda is integral and has exactly the original generic field. Finite presentation of T_lambda over S is neither claimed nor needed by 01ZM. Only the schemes being compared must be finitely presented over T_lambda.

The current main-20261015 blueprint changes lem-trf-local-term-locality to the contracting-correspondence argument. This item's historical normalization ancestry is already recorded in its blueprint.from.place and retained. I am splitting the assigned general tool, not changing that unit or reviving its old nearby-cycle argument. Generic tools of other units are declared in split_report.tool_uses; maintainer-owned tool_uses and unit records are untouched.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches included finite modification, finite generic, reduced fibres, normalization, isomorphism locus and schematic closure. Existing relative normalization, integral subalgebra approximation, scheme-image kernel, partial-section image, flatness, gluing and limit-descent nodes suffice. The schematic-closure blueprint hits concern an already open immersion or compactification; the needed projection-over-an-open statement is already lemma-nagata-scheme-image-partial-section, which is cited. The birational quasi-modification common-cover and valuation normalized-graph nodes have different inputs and do not replace it.

## Mathlib reading

All new searches were run with msearch.py and appended as returned to searches.jsonl, then recorded with their exact tool/query (and subdirectory for grep). Both the geometric and algebraic phrasings were tried. LeanSearch returned normalization interfaces, the definition of geometric reducedness, flat base change, finite morphisms and separated diagonals; LeanFinder returned scheme gluing, finite pullback projections, normalization, and tensor-product integral-closure statements. I read the relevant Mathlib finite-morphism and scheme-theoretically-dominant source, as well as the project's Pullbacks.lean graph statements. None states the finite-base reconciliation theorem or a one-line specialization. The Loogle patterns returned zero hits; both broad graph grep patterns and eta-modification grep were read. No unavailable service was counted as a negative mathematical result. No node was created for these searches.

## Unfinished work

No mathematical gap is deferred into a new lemma in this delivery. The cited existing nodes remain the designated dependencies. The archival Temkin copy is WANTED as above. Server dry-run and delivery results are reported below when available.

## Review by Q47

I read the item against Temkin Corollary 3.5.4 (integral qcqs base, flat finitely presented target, two finite generic modifications, flat geometrically reduced sources) and Theorem 3.5.5 Step 1 (finite cover, additional finite base modification, gluing). I also read local Stacks morphisms.tex at lemma-integral-closure (035F), lemma-characterize-normalization (035I), lemma-normalization-normal (035Q), lemma-quasi-compact-scheme-theoretic-image (01R8), and lemma-scheme-theoretic-image-of-partial-section (0CNG); properties.tex at lemma-integral-algebra-directed-colimit-finite (0817); limits.tex at lemma-descend-finite-presentation (01ZM) and the limit lemmas 01YW/01YX; schemes.tex at lemma-glue (01JB) and lemma-glue-schemes (01JC). The imported node supplies the same hypotheses and all the resulting clauses. There is no new statement to source-check or leave unsplit.

1. The empty covering really forces Z empty. Identity base change and the empty scheme satisfy all assertions, including schematic density, without a nonemptiness assumption on any family fibre.

2. I opened the qcqs permanence statement: its clauses (1)–(3) give exactly the source/target qcqs and base-change facts used. The affine-morphism permanence node gives quasi-compactness and separation of finite maps, since finiteness includes affineness. The flatness and finite-presentation definition nodes really define those properties using local rings and affine neighbourhoods, so restricting their source opens requires no extra theorem. Pairwise intersections need only be quasi-compact, not affine. This is why the later use of 01ZM is for general finitely presented schemes rather than just algebras.

3. The local-ring affine-neighbourhood limit node includes nonemptiness, directedness, affine transitions, qcqs objects and the limiting cone. At the generic point of an integral scheme its local ring is the function field. The statement of thm-pd-spreading-out has both morphism descent and eventual equality, so it descends not just a putative inverse but its two inverse equations. Taking a common later affine index works because the index family of inverses and equations is finite. No generic-open theorem is assumed without a citation.

4. The torsion-free-sections lemma applies to any flat scheme over a domain and to every nonzero base element; it does not require properness, finite presentation or a valuation base. On an affine chart the zero-localization criterion supplies one nonzero annihilator for each section. With L=O this yields the claimed injection; the sheaf axiom passes it to arbitrary opens. The conclusion concerns schematic, not just topological, density. This also justifies the elementary flag: the only theorem being used is cited, and the remaining argument is the localization criterion plus restriction.

5. The relative-normalization statement gives integrality and the affine integral-closure formula, as well as integrality of the resulting scheme when its input is integral. Its input eta to S is affine, checked on nonempty affine opens of the integral base. The finite-normal-product integral-closure statement is stronger than the singleton-field instance used here and explicitly asserts that every prime localization is an integrally closed domain; I did not infer normality from a definition node. Affineness and the qcqs permanence clauses then give precisely the compactness hypotheses for 0817.

6. I checked clause (1) of integral-algebra-directed-colimit-finite, which uses actual subalgebras. The relative-Spec anti-equivalence gives the schemes and transition morphisms and their affine descriptions. The finite-permanence-over-separated statement makes transitions finite. Quasi-coherent-algebra-colimit states the affine section formula; spec-colimit-limit and limit-affine-transition supply the resulting affine-local limits; scheme-morphism-gluing glues the unique local factorizations of every cone and thus proves the global limit property. Because the algebras are subrings of K containing R, their generic localization is K and they are domains. The component schemes therefore have one generic field and are integral, not arbitrary finite fp approximants. This step does not assume a finite normalization.

7. Finite-morphism permanence supplies precisely finite base change. The geometric-reduced-fibre-locus-base-change statement allows arbitrary base change, so it applies to N even if N is not finite over S. Restriction to an open fibre preserves reducedness because its local rings are the same. The eta-normality node's opening assertion is for a normal integral base and any flat finitely presented family with reduced geometric fibres; both source models on every overlap meet these hypotheses by step 2. The graph is taken in F_i times_H F_j, not in a product over the wrong base. Its quasi-compactness follows from its qc source and qs target, the exact assertion of the cited permanence node. The scheme-image node supplies the closed image and its kernel formula, with no unproved use of its internal construction.

8. The closed-immersion-finite node, finite base change and finite composition give both finite projections of G. The existing partial-section image node applies because the overlap of the good base open is a qc open of each source and the other finite map is separated. It says exactly that the projection over this open is an isomorphism, and symmetry supplies the other projection. The scheme-image kernel statement, combined with the affine-quotient clause in the closed-immersion definition, proves injection into sections on the graph open. Thus schematic density holds also on G, not just on the flat F_i. Finite-proper supplies properness, and the good open contains the whole generic fibre. Only after all three conditions of a finite eta-modification are verified is the eta-normality assertion invoked. The two projections becoming isomorphisms is the comparison argument, not an assumed comparison theorem.

9. The same affine torsion-free injection applies to restrictions of the flat source over N or over the later integral S'. Maps over H between two finite H-schemes become algebra maps on inverse images of affine opens. Their generic maps are forced to coincide, and injection on the target of the algebra maps gives equality. Scheme-morphism-gluing explicitly provides equality from an open cover. This proves uniqueness and the triple-overlap cocycle without assuming the latter as gluing data.

10. I checked both clauses (2) and (3) of thm-pd-spreading-out, with all overlap models and comparison targets finitely presented as established in step 2. Both inverse identities and compatibility with q are descended; no claim about an arbitrary map becoming compatible by fiat is made. A finite list permits one index. The generic fibre of that integral T_lambda is eta by step 6; finite-proper and its closed image then give surjectivity. Uniqueness from step 9 applies over this integral, possibly nonnormal S', and proves both the cocycle and the agreement with the originally chosen good-open identifications.

11. I compared the full glue-schemes statement, including its inverse-image condition on three opens, with the proposed data. Base-preserving overlap maps make that condition the inverse image of the triple intersection. The scheme-morphism gluing node produces q. Its inverse image of each H_i is exactly F_i, checked by representatives on overlaps; this is needed to use finite-local-on-target, whose statement is exactly locality under arbitrary open covers. The generic isomorphism is inherited from the given finite maps and their identities.

12. Flatness and local finite presentation are checked by the actual local-ring and affine-neighbourhood definitions on the open charts F_i. They are not inferred merely by naming them source-local. Finite q is affine and thus qcqs by affine permanence, and qcqs permanence gives Y qcqs and its map to the qs base qcqs. This supplies global finite presentation. Base-change preservation of geometric reducedness followed by the reduced-scheme-open-cover statement applies separately on each geometric fibre, including empty ones.

13. Over V' each q_i already has an inverse and step 10 identifies the overlaps by that inverse, so the scheme-morphism gluing statement glues the inverses as well. The target Z_S' is flat by the base-change node, and the source is flat by step 12. Step 4's calculation therefore proves both schematic-density clauses for the same U. I did not replace target density by source density or silently drop either clause.

I tested S a field (the given maps are already isomorphisms), S normal (the comparison can be made immediately over S), a nonnormal integral base with nonfinite normalization (the subalgebra limit, not finiteness of normalization, is used), an empty cover, empty charts, empty overlaps and empty fibres. The proof uses no Noetherian hypothesis, no finite-type-over-a-field hypothesis, no dominance of Z beyond what flatness permits, and no separability assumption. All thirteen steps are below 2000 characters; none hides a new lemma, and the common-graph argument is expanded in steps 7–8. Every proof use has its verbatim citation in citations.json; there are no tag-only dependencies. No new node duplicates a clause of the item. No SGA source is used.

## Validation

The initial server dry run exited 0 with OK (not pushed), commit 5d3af7c7f3. Before the final run I made the gluing of the affine-local limit factorizations in step 6 explicit and added that step's verbatim citation of lem-weil-pbc-scheme-morphism-gluing. The unchanged statement, dependency union, preservation of original fields, citation coverage and maximum step length were checked in the sandbox.
