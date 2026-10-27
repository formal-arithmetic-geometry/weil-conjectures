# Q36 stage-1 delivery: lem-sfb-space-quasiaffine-fp-envelope

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-quasiaffine-fp-envelope.json: item, split into five steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-quasiaffine-affine-factorization.json: statement, unsplit; no Mathlib match for algebraic spaces (086S).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-fp-limit.json: statement, unsplit; no Mathlib match for algebraic spaces (0870).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-eventual-closed-immersion.json: statement, unsplit; no Mathlib match for algebraic spaces (0828(1)).
- dag/nodes/sec-six-functors-basics/lem-sfb-space-qc-open-finite-presentation.json: statement, unsplit; no Mathlib match for algebraic spaces (06CN).

The sandbox also contains citations.json, the actual searches.jsonl, saved complete search responses and the writing script. These are supporting records, not library edits. Four new nodes, zero Mathlib leaves.

## Attachments

None. I searched the live project source under lean/WeilConjectures for the blueprint id, quasi-affine terminology and finite-presentation envelopes. The envelope code in AlgebraicGeometry/SeparatedEnvelope.lean and NoetherianApproximation is for schemes. It does not prove this statement for algebraic spaces over an algebraic-space target. No Lean was written or compiled.

## WANTED

None: all mathematical sources used are present in literature/stacks-project.

## Findings and changes

The original item had no proof. Its statement agrees with Stacks 0871, spaces-limits.tex, label lemma-quasi-affine-closed-in-finite-presentation, lines 2791 onward. I kept it exactly, including a general qcqs algebraic-space target, local finite type rather than finite presentation of the original map, and no extra separation assertion about the resulting envelope. There is no statement dispute.

The source writes U = lim U_i after having called the source X; the intended restricted limit is X. The split consistently calls it A. The source's final sentence also leaves implicit why the chosen open is finitely presented over the target. Step 5 supplies the needed quasi-compactness, finite presentation of a quasi-compact open immersion, and composition citations.

The computed blueprint ancestor is null: tools/blueprint_refs.py ancestor prints that a new node has blueprint.from.node = None. The item's inherited provenance passes through a long created-item chain. I retained that null ancestor and the complete inherited via list and place, appending the exact supporting sentence of 0871 for each new node. I did not invent a blueprint node. I read the current latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof, in addition to the DAG unit/chapter records. This split supplies a foundational approximation tool below the inherited alteration route; it changes no unit or chapter route.

## Not duplicates

lem-sfb-space-eventual-closed-immersion vs lem-sfb-space-closed-limit-stabilization: the existing node is 0828(3), assumes closed transition maps and a locally finitely presented limit over B, and concludes that projections are isomorphisms. The new node is 0828(1), allows arbitrary affine transitions, assumes only local finite type for a closed subspace of the limit, and concludes eventual closed immersion. Neither its stronger local finite presentation hypothesis nor its closed-transition hypothesis is available here. I opened its full statement after the dry run exposed this newly present same-tag node.

lem-sfb-space-quasiaffine-affine-factorization vs lem-sfb-space-quasiaffine-fp-envelope: the new node gives an open embedding in an affine morphism with no finite-presentation requirement, for any quasi-affine map. The item requires local finite type and a qcqs base and gives a closed embedding into a finitely presented morphism. The first is the affine-envelope construction used before the approximation and eventual-closed argument; it does not restate the item or one of its clauses. The shared 0871 tag in its source identifies where the 086S consequence is used.

lem-sfb-space-eventual-closed-immersion vs lem-sfb-space-eventual-monomorphism: both source 0828, but the new node is clause (1), assuming a closed immersion into the limit and quasi-compact stages, and concluding closed immersion at late stages; the existing node is clause (4), assuming a monomorphism, quasi-separated stages and a quasi-compact source, and concluding only monomorphism. That conclusion cannot supply the closed immersion needed here.

lem-sfb-space-quasiaffine-affine-factorization vs lem-trf-quasi-affine-relative-spec-embedding: the existing equivalence concerns schemes X and S; the new fact permits algebraic spaces X,Y, including a non-schematic target, and is not a specialization of the scheme statement.

lem-sfb-space-affine-fp-limit vs lem-sfb-space-finite-fp-approximation: the existing node assumes a finite morphism and gives finite stages with closed-immersion transitions; the new result applies to arbitrary affine morphisms, with affine finitely presented stages and no finiteness or closed-transition conclusion.

I searched all DAG sources for 086S, 0870, 0828, 06CN and their exact Stacks labels, and all DAG statements for the same concepts. For 0827 I reused lem-sfb-space-limit-open-cover-descent instead of creating a single-open version. I searched the whole imported blueprint with blueprint_refs.py for those tags, quasi-affine finite presentation, algebraic spaces affine, open immersion presentation, closed limit, affine approximation and quasi-affine factor. The returned approximation/open-descent blueprint nodes concern schemes or other statements. No blueprint node states a new node here. The new nodes have same_as = [].

## Review by Q36

I read the proof of Stacks 0871 in spaces-limits.tex and followed its five operations in order. This is a split of its argument, not a new lemma reproducing its conclusion. Each supporting node lacks the original theorem's combination of hypotheses and conclusion: 086S constructs an affine envelope without a finite-presentation assertion, 0870 treats an arbitrary affine map without a closed source embedding, 0828(1) is an eventual property of an already supplied system, and 06CN concerns an already supplied open immersion. All four new nodes carry statements only, with empty proof/proof_deps and null proof_origin.

For the affine-factorization node I read 086S in spaces-morphisms.tex, label lemma-characterize-quasi-affine (around line 4054), including its reduction to 01SM. A quasi-affine morphism is quasi-compact and separated on affine scheme tests, so it is within the characterization's qcqs scope. Its canonical affine envelope gives the required factorization. The node intentionally records existence, without claiming the envelope affine morphism is finitely presented. In step 1 I also opened lem-sfb-space-affine-locality and used exactly its last sentence, affine over qcqs implies qcqs. I opened lem-sfb-space-quasicompact-fppf-local: its stated test over every quasi-compact algebraic space justifies pulling the quasi-compact open immersion back to a qc atlas and obtaining quasi-compact A. No finite-type assumption on Z is used.

For the affine-approximation node I read 0870, label lemma-affine-morphism-is-limit (around line 2700), and its relative-spectrum construction from finitely presented algebras. It gives affine finitely presented B-stages and affine transition maps. The index is small and nonempty in the project's size convention. Step 2 again uses affine-locality for qcqs stages. I read the full statement of lem-sfb-space-limit-open-cover-descent: it requires a finite covering family, so citing it for A alone would be wrong. I corrected that potential C4 error by applying it to A,Z, whose union is Z. Both are quasi-compact opens of the qcqs limit. Its first clause gives U_i0; its last clause gives the later inverse images' qcqs property and affine transitions. Its source is 0827 (lemma-descend-opens), read in spaces-limits.tex around line 1078. No new descent node is necessary.

In step 3 I used only that same node's explicitly stated inverse-image clause. The identification of the restricted limit with A is written out on test-scheme sections: compatible tuples have exactly the condition that their i0-component lies in U_i0. Passing to the tail is valid because a directed tail is cofinal; compatible maps/tuples extend uniquely using an upper bound with i0. This is a formal sheaf-limit argument, marked elementary, and does not import a hidden geometric limit theorem. Every U_i is an open subspace and hence an algebraic space, by the open-subspace definition used in the new nodes.

For eventual closed immersion I read 0828, lemma-finite-type-eventually-closed, clause (1), around lines 1235-1271. Step 4 uses that precise clause with common base B, stages U_i, source A and the identity of its limit. The identity is a closed immersion on every scheme test. The stages are quasi-compact, transitions affine, and the source map A to B is the given locally finite type g; no assertion that g is locally finitely presented or B is a scheme is used. I opened the existing eventual-monomorphism statement: it cannot replace clause (1). This is the one same-source-tag pair listed above.

For the final supporting node I read 06CN, lemma-open-immersion-locally-finite-presentation, spaces-morphisms.tex around line 5651. Open immersions are locally finitely presented on charts; their relative diagonal is an isomorphism and hence quasi-compact. With quasi-compactness assumed this is finite presentation. This is a general fact about algebraic-space morphisms rather than a clause of the item. In step 5 I opened lem-sfb-space-qcqs-permanence, whose first implication says a map from a quasi-compact space to a quasi-separated one is quasi-compact; U_i and Z_i meet these hypotheses. I then opened lem-sfb-space-separated-fp-composition: its finite-presentation composition clause does not require separatedness, despite the node's name. It applies to U_i to Z_i to B. The equation v e = g follows from the B-compatible projections, not an identification of underlying point images.

I tested the new statements on the empty source, empty stages/base, and a constant singleton directed system. Empty opens are allowed; the family A,Z still covers Z when A is empty, and the identity of the empty limit is a closed immersion. In a constant system the eventual property is its original closed immersion. For an arbitrary non-Noetherian affine base, 0870 and 06CN impose no Noetherianity; the argument never concludes that a closed immersion is finitely presented, only the open inclusion. For an affine map not of finite type, 0870 still allows infinitely many generators via a directed system. For a non-schematic qcqs target, all four geometric facts are the space versions in spaces-limits/spaces-morphisms, not scheme-only analogues. I verified that no new node assumes the conclusion of the item and no cited statement depends back on the item.

I reviewed delivery-errors B through E: the new statements introduce all objects and define or cite each notion; their sources use the exact labels/tags read; TeX has single backslashes. Searches were actually run through msearch.py, twice semantically for each statement, with Loogle, source grep and LeanSearch, and their complete results are saved. I read the hits, including Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean lines 40-64: the open-immersion instance at line 62 is scheme-only. AffineTransitionLimit and QuasiAffine hits likewise concern Scheme. They do not specialize to the new algebraic-space statements. No search was invented and no unavailable service was called a negative result. citations.json contains the verbatim full statement for every step/node pair, so that all used clauses can be read directly. Every step is under 2000 characters and has an explicit argument; no large inline auxiliary lemma remains. No SGA source, Lean writing, compiler or library build was used.

## Unfinished work

Only the intended four statement-only descendants remain unsplit. No part of the item's natural-language proof is deferred. Required server dry run and direct delivery are the next operations.
