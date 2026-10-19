# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-fixed-cocone-opposite-limit.json`: existing statement item, now split into five steps; Mathlib verdict: no match for the coherent comma quasicategory statement. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every node cited in every step.
- `report.md`: this report. `searches.jsonl` was written by the required msearch commands.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for quasicategory, pinched, fixed-cocone and cocone-opposite concepts found no declaration of this statement. The project declarations encountered by the broader opposite/colimit search concerned ordinary categories. No Lean was written or compiled. Upstream master was treated as reference material only.

## Wanted sources

WANTED: archived Kerodon Construction 1.4.2.2 (003N), for the simplicial opposite convention used by lem-coef-infinity-fixed-cocone-opposite-limit. Read online at https://kerodon.net/tag/003N on 2026-10-17.

WANTED: archived Kerodon Subsection 7.1.6 (02KF), particularly Remark 7.1.6.2 and Example 7.1.6.5, for comparison with opposite duality and the empty-shape check. Read online at https://kerodon.net/tag/02KF on 2026-10-17. These are Kerodon identifiers, not Stacks tags. No Stacks result is asserted to provide this quasicategorical comma isomorphism.

## What was wrong or changed

The imported item had no proof. Its statement is correct with its explicitly specified coherent comma definitions, and remains verbatim unchanged. I retained its existing source, ancestry, original Mathlib searches, and all other protected metadata. Its inherited split_report named the parent item; that split-owned field now describes this item's five-step proof.

The proof is marked agent-written. Kerodon 003N supplies the definition of opposite and 02KF Remark 7.1.6.2 supplies duality for sharp relative cones. Neither is presented here as a published theorem identifying our coherent comma pullbacks. The identification is established on the actual parameter simplices, and the universal-property assertion uses the exact initial/terminal conventions of def-cbc-enhanced-diagrams-cones.

The main-20261015 ancestor is now filed under `sk-thm-sf-package`; I read its paragraph 2 (the derived coefficient-adjunction mapping object calculation), as well as the historical ancestor and the current inherited unit/chapter records. This is a local foundations tool for its coherent realization. I did not change unit or chapter metadata or replace any unit-level proof step.

## What could not be finished

Nothing remains for this one-level split. The pre-existing internal-functor reversal and relative-cone-equivalence nodes remain dependencies to be handled in their own items; their statements, rather than their proof internals, are used here.

## Not duplicates

No new nodes were created. Searches of the whole DAG by 003N/02KF and opposite/cocone terminology and `tools/blueprint_refs.py search` for fixed cocone, fixed-boundary opposite, colimit limit, and opposite found no imported blueprint node stating this item. The generic opposite search returned nineteen unrelated ordinary-category or geometric opposite constructions, hence `same_as` remains empty.

The existing lem-coef-infinity-cocone-opposite-join-functor already states internal-functor reversal, so it is cited rather than copied into a new node. Lem-coef-opposite-join-comma-comparison also states the cone-to-cocone opposite identification while comparing sharp/fat join cones. It does not state the outgoing/incoming mapping-space equivalence or the fixed-cocone colimiting/limiting criterion; no separate node duplicating its comma-isomorphism clause was created. Here the short degreewise construction is part of the proof of the full existing item.

## Mathlib searches

The seven searches run for this item by msearch.py are retained exactly in searches.jsonl and appended to the inherited mathlib_searches records. The two semantic phrasings distinguish coherent comma quasicategories and their mapping spaces from ordinary categorical cones. LeanFinder, LeanSearch and Loogle were available. The ordinary-category candidates were read in Mathlib/CategoryTheory/Limits/Cones.lean (coconeEquivalenceOpConeOp, line 769, with Category instances for both source and target) and Mathlib/CategoryTheory/Limits/HasLimits.lean (IsColimit.op, line 1054). They do not apply to an arbitrary small simplicial indexing set or supply the coherent mapping spaces in the item. The second semantic search also found SSet.opEquivalence and opFunctorCompOpFunctorIso; I read Mathlib/AlgebraicTopology/SimplicialSet/Op.lean, where these give only the simplicial opposite involution. The targeted grep in AlgebraicTopology/Quasicategory for cones, limits and opposites returned no hits. The broader quasicategory grep found basic, nerve and strict-bicategory developments; I read Basic.lean to verify these are foundational quasicategory definitions rather than the requested comma/limit result. These facts do not make the whole item a one-line Mathlib specialization.

## Review by Q92

I read the item's full statement, its three statement dependencies, the coherent functor/cone calculus statement, the current and historical blueprint ancestor text, and the two Kerodon source pages named above. For the item the source-intended distinction is essential: the statement concerns the literal coherent comma pullback of transformations, not a sharp join slice. I checked all endpoint equations directly using the stated pullback definition. There are no new node statements whose sources or hypotheses require a separate review.

Step 1 cites def-cbc-enhanced-diagrams-cones to name the two fixed-diagram pullbacks, clause (4) of lem-coef-infinity-relative-cone-equivalence for the fact that the target opposite is a quasicategory, and lem-cbc-enhanced-functor-cone-calculus for functor- and coherent cone/cocone-category closure. Its statement explicitly asserts closure for every small shape and the dual cocone assertion. K need not itself be a quasicategory. The universe containing E can also contain K and both functor objects, so no small-index hypothesis is lost. The calculus is an off-unit generic tool; the reason for using it is declared in split_report.tool_uses. I removed an unnecessary assertion about the pinched mapping models being Kan from this setup step, so the proof does not take a broader Kan claim from an ambiguous pronoun in the calculus statement.

Step 2 uses the exact internal-functor reversal clause of lem-coef-infinity-cocone-opposite-join-functor, not its join-collapse clause. I checked its degree-n formula against the diagram h on K times the parameter simplex times the interval. The definition node gives precisely these simplex data; the relative-equivalence node defines opposite by conjugating simplex operators. Applying opposite preserves products coordinatewise. Reversing the interval takes original endpoint 1 (the varying constant apex) to new endpoint 0 and original endpoint 0 (the fixed diagram) to new endpoint 1. Thus the fixed boundary is exactly F^o and the varying apex is exactly a^o. No strict fiber is substituted for a homotopy fiber, and no cylinder data are discarded.

Step 3 uses only the opposite operator formula already quoted from clause (4). I checked the displayed identity on each vertex: both sides are n-alpha(i). This gives compatibility with every face and degeneracy, with the source using alpha^vee. The inverse is literally the same double reversal, and apex and endpoint evaluations are computed coordinatewise. This is an elementary verification on the formulas, not a theorem about arbitrary strict pullbacks preserving equivalences. Restriction of shapes and postcomposition of the target commute with those formulas. No hidden comparison lemma is invoked.

Step 4 uses clause (4)'s actual statement of natural mapping-space equivalences for every quasicategory, with D there instantiated as C_F. This reverses Map(C_F)(lambda,mu) to Map(C_F^op)(mu,lambda). The isomorphism of step 3 then takes it to Map(L_Fo)(mu^o,lambda^o); its inverse preserves the right-pinched constant initial face and final vertex, as specified by the definition node. The equivalence here is not claimed to be a strict equality between left- and right-pinched mapping spaces. Naturality is precisely the naturality asserted by the cited node followed by the single simplicial isomorphism. The initiality and terminality definitions are explicitly present in def-cbc-enhanced-diagrams-cones. Because Phi is bijective on vertices, their quantifiers range over all the same cocones/cones; the contractibility equivalence follows from the definition of weak equivalence via components and homotopy groups. I did not use the join-relative universal-property clause of the relative-equivalence node to identify two different cone conventions.

Step 5 uses only the internal functor and comma definitions: Fun(empty,E) is the terminal simplicial set degreewise, so the two comma categories are E and E^op. It is an elementary check, not an existence theorem for unrelated limits. I also tested K=Delta^0 with E the nerve of the poset 0<1: the cocone edge 0 to x reverses to x to 0, and the identity at 0 is initial in the first cocone category and terminal in the opposite cone category. For E terminal all data are unique. For E empty and K nonempty there is no diagram F; for K empty the comma categories are empty and the isomorphism still exists, with no universal object falsely produced. These cases check that no nonemptiness, pre-existing colimits or limits, or discrete-diagram hypothesis was silently introduced.

I checked B1-B10: there are no new nodes, no hollow data or attachment claim, the item is self-contained with its existing definition dependencies, and only actual searches are recorded. For C1-C8 I checked each cited statement above and produced exact statement quotations in citations.json, kept proof_deps equal to the union of uses, and declared the sole off-unit theorem tool. For D1-D5 the argument stays in this item's steps rather than relocating any of its clauses into new nodes. For E1-E7 I checked smallness and opposite universes, interval variance, fixed diagram versus varying apex, and the empty cases above; no source or statement correction is needed. Each proof step is below 2000 characters, and none hides a standard-lemma invocation. The mathematical changes made during this self-review were the explicit simplex-operator identity and the removal of the unnecessary Kan assertion from step 1.
