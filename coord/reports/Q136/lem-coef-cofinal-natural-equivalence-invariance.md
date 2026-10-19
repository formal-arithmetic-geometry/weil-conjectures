1. Files written:

- `dag/nodes/sec-six-functors/lem-coef-cofinal-natural-equivalence-invariance.json` — statement split; no new nodes; Mathlib searches found no matching quasicategorical result.
- `citations.json` — verbatim citations for every proof-step dependency.

Attachments: none.

WANTED: the archived source for Lurie, *Higher Topos Theory*, Corollary 4.1.1.10 and Proposition 4.1.1.8 (the current source is read online).
WANTED: an archived Kerodon/HTT source for the coherent mapping-space and colimit comparison used in the proof.

The item statement was retained verbatim. Its exact comma object is the source-fixed pullback
`{b} ×_{B,ev₀} Fun(Δ¹,B) ×_{ev₁,B,w} A`, with the stated enlarged-universe convention. No declaration in either read-only Lean source checkout carries the blueprint tag, and no existing DAG node states this natural-equivalence invariance as a whole. The saved Mathlib searches were reused after reading their results; ordinary-category `final_natIso_iff` and related hits do not specialize in one line to coherent quasicategories and weakly contractible simplicial comma objects.

## Review by Q136

I read the item node, its dependency [def-cbc-enhanced-diagrams-cones], the unit and chapter records, and the complete statements of [lem-coef-infinity-cofinality-space-test], [lem-coef-space-transport-classification], and [lem-cbc-enhanced-functor-cone-calculus]. I also checked the ancestor blueprint route for the filtered coherent-section/cofinal-evaluation tool and read the cited HTT and Kerodon source pages online. The server-side `check_dag` and `review_split` checks both pass.

Step 1 uses precisely the equivalence of the universally quantified conditions (3) and (4) of the cofinality space test, together with the transport-classification statement identifying that mapping diagram and its arrow model. I corrected the earlier pointwise reading: the cited statement does not assert a pointwise equivalence between the comma object and the colimit. The hypotheses that (A,B) and the equivalence data fit in an enlarged universe were checked against the item and the dependency's universe convention.

Step 2 uses the functor-cone calculus statement that an equivalence edge in an internal functor category is componentwise an equivalence, and the transport-classification statement that a component (u(a)\to v(a)) acts on (H_B(b,-)) by postcomposition, including higher simplices. Thus the two space-valued diagrams are coherently naturally equivalent.

Step 3 uses the dual cocone and mapping-space criterion in the functor-cone calculus statement. I replaced the uncited Yoneda invocation with the explicit universal-property argument: compose a colimit cocone with an inverse equivalence of diagrams; precomposition and its inverse identify the mapping-space tests, so the resulting cocone is colimiting with the same apex. The cited contractible Kan subcategory of initial objects identifies this apex with any other chosen colimit of the second diagram. This is the only comparison step; it does not assume strict naturality or discard higher coherences.

Step 4 is elementary once Step 1 and Step 3 are in place: an equivalence preserves contractibility, and the conclusion is then quantified over every vertex (b\in B). I checked the empty-index, point-index, identity-functor, and discrete-category cases; the comma orientation and the iff conclusion remain correct. Every non-elementary step cites the statement that supplies its input, every proof dependency is listed, and each citation quote in `citations.json` is verbatim. No step exceeds the 2000-character long-step review threshold. The imported statement remains unchanged. I corrected the pointwise wording of Step 1 and the uncited Yoneda invocation in Step 3; no new node was created. Rechecking the current repository found the item still unsplit with the same statement and dependencies, and searches of the project Lean source found no attachment. The saved search results were retained without rerunning unchanged searches.


The current-source check read Kerodon 04K3 and 02NZ online, confirming the universally quantified corepresentable criterion and the exact oriented comma model. These are Kerodon tags, not Stacks tags; no Stacks source or SGA route is used. The statement has no blueprint_update field in the current repository. Steps 1–4 remain below 2000 characters. The initial required dry run passed at 0844cb321a; the repaired text is submitted to a fresh final dry run before push.
