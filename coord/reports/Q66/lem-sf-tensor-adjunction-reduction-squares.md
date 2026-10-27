# Q66 stage-1 report

Item: lem-sf-tensor-adjunction-reduction-squares. Date: 2026-10-22.

## Files written

- dag/nodes/sec-six-functors/lem-sf-tensor-adjunction-reduction-squares.json: statement item, now split into nine steps; Mathlib searches found related categorical and ordinary sheaf declarations, but no match for this completed integral/strict semilinear-system assertion.
- citations.json: one record per step/node citation, with verbatim statement excerpts.
- report.md and searches.jsonl: review and actual search log. write_split.py is a sandbox-only generation aid, not a DAG delivery file.

There are zero new nodes and zero new Mathlib leaves. The statement and its statement dependencies are unchanged. Every inherited field, including the source and blueprint ancestry, is retained. The item is not its unit's key node, so no unit record is changed.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag/id, semilinear systems and reduction/coefficient associator/compositor terminology. The StageSystem/Basic.lean hit concerns filtered common-field-stage pair categories, not the inverse quotient-system adjunction here. No declaration found states all the item's clauses without sorry.

## WANTED

None. The proof is explicitly agent-written. Its blueprint source and the Stacks sources used for the categorical and ringed-site normalization checks are available locally; no unavailable text is presented as a proof read.

## Problems corrected and scope

The imported item had no proof steps. The blueprint's maps-used sentence does not itself supply the whole-system comparison calculation. A finite list of evaluated coefficient equalities would not prove equality in the derived category of systems, so the split uses the actual reduction/limit Hom bijection throughout.

There is no statement correction or disputed mathematical claim. The word domain permits proper direct-image vertices. Accordingly an occurrence of a P_v/S_v unit or counit must have endpoints in that domain, hence its S_v vertex is proper; the proof makes this existing typing restriction explicit. It does not claim an integral comparison for a nonproper direct-image vertex outside the word domain.

The primitive transpose equalities are hypotheses of this item. The split does not reprove them or cite lem-sf-primitive-reduction-transpose, and does not cite the parent lem-sf-generator-reduction-coherence. Similarly it does not use the parent item's eventual arbitrary-expression coherence. A read-only dependency traversal found no path back to this item from the reconstruction, substitution, bridge, open comparison or generic mate tools.

A draft argument for direct-image composition expanded the mate word and would have needed care about additional normalized intermediate objects. I replaced it with the mate's natural Hom characterization. Only the given proper-image endpoints/subwords and the pullbacks of complete test objects are needed; the latter have their realization supplied by the general substitution theorem itself. The primitive hypothesis is not extended silently to arbitrary test inputs.

## Not duplicates

No new nodes were created, hence there are no new/existing-node pairs to distinguish. Whole-DAG and blueprint searches for tensor reassociation, normalized systems, total-limit, completed-operation and the item's title found existing tools, which are cited rather than restated. In particular lem-pur-completed-operation-tower-substitution supplies the tensor/pullback realization, lem-pur-normalized-reconstruction-adjunction-calculus supplies the actual equivalence and adjunction calculus, and lem-sf-integral-open-reduction-comparison supplies the open normalization. None is recreated as a clause-shaped new node.

## Review by Q66

I read AGENTS.md, the worker role and brief, stages/1-dag.md, the three blueprint levels in SETUP.md, GOAL.md, delivery-errors.md B--E in full, the chapter and unit records, and fix-prop-coherence.proof.md in main-20261015. The unit's coefficient-compatibility route is preserved: this item treats only tensor constraints, pullback composition, the two ordinary geometric adjunctions and direct-image composition. No SGA source is used. I also read the available Stacks categories.tex passages for Tag 0037 (definition-adjoint), Tag 0DV0 (lemma-compose-counits) and Tag 0B65 (lemma-transformation-between-functors-and-adjoints), and sites-cohomology.tex at Tag 0D6D (lemma-derived-pullback-composition), Tag 0FPI (lemma-adjoints-push-pull-compatibility) and Tag 0GL1 (lemma-j-shriek-and-tensor). Their tag/label correspondence was checked in tags/tags. They explain the adjunction and representative normalization; all non-elementary facts in the actual split are cited DAG statements. There are no new nodes needing a separate source review.

For each step I opened and read the statements of its cited nodes:

1. The reconstruction-calculus statement explicitly gives an adjoint equivalence with the actual u and e invertible on complete/normalized objects. The substitution statement includes the coefficient unit system. These give invertibility of the primitive comparisons, completeness of basic outputs through d_A, and invertibility of the finite recursive comparisons. The hypotheses assume normalization at the actual intermediates; I did not infer global preservation by S_v.
2. The evaluation-calculus statement gives the actual adjunction and triangle identities on derived systems. Applying its two Hom transposes and naturality proves the displayed q recursion and the transpose criterion. The calculation is written out and marked elementary. This is not an inference from the faithfulness of evaluation.
3. The substitution statement explicitly says that completed tensor associators and action unitors are limits of canonical system maps and that its identifications are natural and compatible with substitution. Its comparisons use tensor of the actual counits. Those are precisely the comparisons obtained from Step 2; thus the independently specified canonical completed maps are identified, not defined anew. The explicit homogeneous tensor formulas serve as a check of the two unit conventions and associator direction.
4. The same node explicitly includes the canonical composition comparison of completed pullbacks and its naturality under substitution. Its hypotheses are normalized systems on schemes with ell invertible; the field/prime hypotheses of this item ensure that. No flatness of a quotient map is assumed.
5. The semilinear-sections statement provides the ambient system adjunction. The reconstruction statement provides the actual complete/normalized Hom equivalences and transported adjunction. The canonical-bridge definition specifically fixes integral proper-image realization by right-adjoint conjugation of the section-normalized comparison. I checked this sentence rather than using the definition node as a substitute for a new preservation theorem. The displayed chain of Hom bijections identifies this pre-existing adjunction on the complete objects where it is being used.
6. The reconstruction-calculus statement contains the explicit transported counit and the actual transpose formula. Taking identities in the preceding Hom bijections and substituting Step 2 gives the written unit and counit equations. The quote in citations.json includes that transpose clause. No equivalence is used to replace the specified u or e by other isomorphisms.
7. The open-comparison statement expressly identifies the realized open unit and counit with the localized completed-ring maps using the corresponding restriction pullback. Its displayed formula for d_j inverts to the same primitive normalization. Its hypotheses are a quasi-compact open, ell invertible and complete inputs, all present here. I also read lem-sf-open-reduction-adjunction-transport as a check of which exact two equations the assertion means; it is not an extra proof dependency, since the cited open-comparison statement already supplies them.
8. The mate-definition statement gives the bijection and its transpose characterization. The mate-pasting statement (2) fixes composition along adjunctions, while semilinear-sections specifies actual system maps rather than lifts from levels. The reconstruction statement gives the composition comparison inserting the actual counit. Together with the whole-system pullback-compositor identification from substitution, these make the three arrows in the written Hom characterization agree. Testing on the source identity proves equality of the two maps. This avoids requiring normalization of all expanded mate-word vertices.
9. Only the established generator equations, functoriality and inverse equations are used. The inverse square is written explicitly. Naturality and quotient transitions come from the actual whole-system maps already identified; no additional coherence theorem is invoked.

I checked delivery-errors B--E against the final files. There are no statement-only-node violations, unspecified new notions, unsearched new nodes, duplicated clauses, or new-node proof sketches, because no new node is necessary. The item retains its exact statement. Every non-elementary step has cited statements that supply its ingredients, every quoted excerpt is literally present in the cited statement, and proof_deps is exactly the union of uses. The proof is marked agent-written rather than attributed to the blueprint as a completed argument. No step exceeds 2000 characters. No hidden comparison lemma is left behind the word “transports”: the reconstruction comparison, canonical adjunction identification and mate characterization are explicit, using their existing nodes.

Small-case checks: zero complexes give zero arrows on both routes; scalar coefficient inputs give ordinary multiplication for both unitors; n=1 and successive quotient maps preserve the pure-tensor formulas without a quotient-flatness assumption; identity proper maps give identity pullback/compositor and identity-adjunction maps; the empty open gives the zero extension/restriction adjunction, and the identity open its identity adjunction. The general proof requires neither nonempty schemes nor nonzero inputs. For reversed composition/tensor identifications I checked the multiplication by inverse maps in Step 9. These are mathematical checks, with no Lean source written or compiler run.

The off-unit reconstruction and substitution statements are generic tools, not replacement geometric routes. Their uses are declared in split_report.tool_uses, as is the generic mate-pasting tool. The blueprint ancestry and the exact maps-used place remain unchanged, with same_as searched and empty.

## Unfinished work

None in the one-level split. Existing cited unsplit lemmas remain their own items. Server-side review_split initially passed with zero new nodes; the final combined delivery dry run and push are performed after this report.
