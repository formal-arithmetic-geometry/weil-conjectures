# Stage-1 report: lem-coef-cosimplicial-frame-mapping

## Files written

All edited files are in the NI item sandbox. The item is split; the seven children are statement-only, unsplit, with empty proof/proof_deps and no proof_origin. There are no new Mathlib leaves.

- dag/nodes/sec-six-functors/lem-coef-cosimplicial-frame-mapping.json: existing statement, unchanged; twelve proof steps; Mathlib searches found no exact match.
- dag/nodes/sec-six-functors/lem-coef-reedy-model-structure.json: statement; general Reedy model structure, relative degree-extension formulas and prescribed degree zero; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-kan-quillen-right-proper.json: statement; Kan-Quillen model structure, lifting descriptions and right properness; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-simplicial-boundary-collapse-test.json: statement; colimit-preserving boundary/collapse criterion; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-bisimplicial-diagonal-equivalence.json: statement; degreewise weak equivalences give diagonal equivalences; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-hammock-infinity-localization.json: statement; arbitrary-relative-category hammock construction and its infinity-localization universal property; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-special-hammock-reduction.json: statement; the nerve of the special three-arrow category computes hammock morphisms; no Mathlib match.
- dag/nodes/sec-six-functors/lem-coef-special-resolution-zigzag-nerve.json: statement; special double resolutions compare to the ordinary special-zigzag nerve, with the actual index-forgetting comparison specified; no Mathlib match.
- citations.json: twenty-one step/node entries, each copying the cited statement verbatim. Full statements are included so the fixed-degree-zero, naturality and comparison-map clauses remain visible.
- report.md: this report. search_results.json retains the search commands' actual outputs; searches.jsonl is the command-maintained execution log. Search and generation scripts are sandbox scratch files, not delivered nodes.

## Attachments

None. I searched both read-only project sources, WeilConjectures in weil-src-slopmaster2 and weil-newtargets-master, for the blueprint tag, cosimplicial frames, homotopy function complexes, Reedy, bisimplicial and hammock terminology. I also checked dag/lean_names_upstream.json. No project declaration states the complete item, and no new helper had an exact project attachment. Upstream sorry declarations were not treated as proofs. No Lean was written or compiled.

## Literature wanted

WANTED: Mark Hovey, Model Categories, Proposition 3.6.8, Theorem 5.2.5/Remark 5.2.3, Theorem 5.2.8, Propositions 5.4.1/5.4.7, Corollary 5.4.4 and Theorem 5.6.2, for lem-coef-cosimplicial-frame-mapping, lem-coef-reedy-model-structure and lem-coef-simplicial-boundary-collapse-test.

WANTED: Denis-Charles Cisinski, Higher Categories and Homotopical Algebra, Theorem 3.1.8, Corollary 3.1.28, Theorem 3.1.16 and the pullback argument in Corollary 3.8.4, for lem-coef-kan-quillen-right-proper and lem-coef-bisimplicial-diagonal-equivalence.

WANTED: Zhen Lin Low, Revisiting function complexes and simplicial localisation, Definitions 3.1-3.2, Lemma 3.4 and Propositions 3.5-3.7, for lem-coef-special-hammock-reduction and lem-coef-special-resolution-zigzag-nerve.

WANTED: W. G. Dwyer and D. M. Kan, Function complexes in homotopical algebra, Sections 4.4, 6.11-6.12 and 7.2, for the comparison route in lem-coef-cosimplicial-frame-mapping and lem-coef-special-resolution-zigzag-nerve.

WANTED: Vladimir Hinich, Dwyer-Kan localization revisited, Section 1.2/Proposition 1.2.1 and Section 1.3.3, for lem-coef-hammock-infinity-localization.

These documents were not found in the local literature collection. I read the relevant passages through the following primary-source online PDFs without downloading files: Hovey https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hovey-model-cats.pdf ; Cisinski https://cisinski.app.uni-regensburg.de/CatLR.pdf ; Low https://arxiv.org/pdf/1409.8062 ; Dwyer-Kan https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-3.pdf ; Hinich https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/hinich.pdf . The item proof is my synthesis and has proof_origin.by = agent. The new statements cite these documents and exact places; none cites SGA. These are model-category results, not claims for which I substituted a nonexistent Stacks tag.

## Errors and changes

I found no counterexample or typing problem in the imported statement, and changed no clause or hypothesis. I retained chapter/unit and the existing maintainer fields. The original unsplit record supplied no argument for its substantial mapping-space assertions. The proof now carries frame existence, coend lifting, Brown invariance, frame independence, the three distinct comparison stages, pullbacks/products and left Quillen compatibility.

An initial version of my compatibility explanation did not justify the action on higher simplices: equality on vertices or the ordinary adjunction would not by itself suffice. I replaced it with explicit comparison lifts between the transported resolution diagrams and target special resolutions. In particular, I do not assert that a left Quillen functor preserves trivial fibrations. The final proof restricts it to cofibrant objects, replaces the fibrant target by a cofibrant-fibrant one, and follows the actual weak-equivalence diagrams into hammocks.

The blueprint reference is to the nearest imported ancestor prop-coef-integral-exceptional-adjoint, current main-20261015 proof paragraph 2 (derived coefficient adjunction in the R Hom/R lim calculation). I read that proof and the item's chapter/unit. The frames are a technical foundation of that calculation through the existing finite-diagram/model-enhancement ancestry, not a replacement of the coefficient or purity route. No changed blueprint statement was bypassed.

## Unfinished work

No part of this item's statement is left unargued. The seven new nodes intentionally await their own one-level splits; they are not claimed proved. Archiving the wanted literature is a maintainer task. This is a stage-1 handoff only; there is no Lean implementation or claim of target completion. The required no-push dry run is recorded below when completed.

## Not duplicates

I searched the whole DAG by model/Reedy, cosimplicial frame, homotopy function, hammock, special zigzag, three-arrow, bisimplicial and Kan/Quillen terminology, and searched the imported blueprint with tools/blueprint_refs.py. No blueprint node states any new helper, so all same_as lists are empty. There are no shared Stacks tags requiring additional pair distinctions.

lem-coef-reedy-model-structure vs lem-coef-direct-wfs-extension: the existing node concerns finite direct categories and a weak-factorization-system extension; it does not supply the full Reedy model structure on Delta and Delta-op, matching objects, the two relative formulas, or the required objectwise consequences.

lem-coef-reedy-model-structure vs lem-coef-finite-reedy-localization: the latter is an ancestor application to finite diagram localization. It does not state the general Reedy structure theorem and cannot be cited back here without a cycle.

lem-coef-hammock-infinity-localization vs lem-coef-model-infinity-derived-adjunction: the latter asserts a derived Quillen adjunction for model categories; the new node concerns universal localization of an arbitrary relative category and gives its actual hammock mapping objects. It supplies no Quillen adjunction or frame theorem.

lem-coef-special-resolution-zigzag-nerve vs lem-coef-cosimplicial-frame-mapping: the new statement has two resolutions, stronger objectwise trivial-(co)fibration hypotheses and an ordinary three-arrow nerve as output; it does not identify a single arbitrary frame's complex with localization, construct frames, or prove the item's Kan/functor/pullback clauses. Steps 2-7 and 11-12 carry these arguments in the item.

lem-coef-special-hammock-reduction vs lem-coef-cosimplicial-frame-mapping: the new statement has no resolution or frame at all. It is a reduction theorem for special zigzag diagrams at arbitrary model-category endpoints.

lem-coef-kan-quillen-right-proper vs lem-coef-cosimplicial-frame-mapping: the new statement constructs the particular model structure on simplicial sets and its right properness; step 10 derives the item's pullback clause explicitly from it. The ground model category is never assumed right proper.

The boundary-collapse and bisimplicial-diagonal statements are general technical results on colimit-preserving functors and bisimplicial sets respectively; neither is a clause asserting that frames compute localization. Object replacements, finite products, quasi-invariance consequences of Brown factorization and preservation of frames were kept as proof steps, not new nodes.

## Mathlib search review

All recorded new-node searches were actually executed by /home/ubuntu/weil-launcher-nt/msearch.py with group NI and this item. Each child has leanfinder, loogle, grep, leansearch and a second differently phrased leanfinder query; actual tool and query strings and outputs are in its mathlib_searches and the execution log. No service failure was relabelled as absence. I read the potentially relevant hits.

In particular, AlgebraicTopology/Reedy/Basic.lean explicitly lists the Reedy model structure as TODO. AlgebraicTopology/SimplicialSet/CategoryWithFibrations.lean gives the lifting classes but explicitly lists the Kan-Quillen model structure as TODO. These are not enough for the new Reedy or Kan model/right-properness statements. CofibrantObject homotopy quotient/localization results concern ordinary hom sets, not the spaces asserted here. SimplicialObject.diagonal is an internal simplicial-object operator, not the diagonal-equivalence theorem for a bisimplicial set. ComposableArrows/Three.lean is the API for three forward composable arrows, not the special weak-equivalence zigzag nerve. Ordinary category localization and the nerve adjunction hits do not supply the infinity-categorical universal property. No exact or one-line specialization was found, so none of these nodes is labelled mathlib.

## Review by NI

I reread delivery-errors B-E against the actual files and primary-source passages, rather than relying on the blueprint's assertion. I read Hovey's Reedy extension/model theorem and the fixed-degree-zero construction for the Reedy child and the existence argument; his boundary/collapse criterion for the coend child; Cisinski's diagonal theorem and Kan model/right properness for the two simplicial-set children; Low's exact special-hammock definition, reduction theorem, special-resolution hypotheses and the Grothendieck comparison for the two zigzag children; and Hinich's derived coherent nerve discussion for the localization child. I also checked the original Dwyer-Kan double-resolution comparison, including its two resolution-cofinality inputs, as a cross-check of Low's route. The special-resolution lemma defines the category I(P,Q) by objects, arrows and their compatibility equation, and records its comparison maps, because merely knowing an abstract weak equivalence would not justify using their construction later. Those seven statements are genuine general technical inputs, not a new name for the frame theorem.

Here is my step-by-step citation and hypothesis check. Step numbers match citations.json.

1. No cited theorem is hidden here: the two factorizations are precisely the model axioms in the item, and the natural replacement maps and two-out-of-three supply the equivalence after localization by its stated universal property.
2. I opened lem-coef-reedy-model-structure and checked that it states the relative latching/matching extension, prescribed degree zero, objectwise trivial fibrations and dual structure. The degree-zero map is explicitly the identity; n=0 uses cofibrancy of X. For positive degree the latching object of the vertex-coproduct diagram is the same vertex coproduct. I wrote the actual induction map. The dual construction makes const(Y) -> B a Reedy trivial cofibration, a property needed again in step 12.
3. The boundary-collapse node really assumes preservation of colimits, boundary cofibrations and simplex-collapse weak equivalences. The written coequalizer verifies the adjunction and colimit condition; representables and their boundaries give exactly A^n and L_n A. The augmentation gives the collapse condition. I did not infer horn lifting just from the word frame.
4. The Kan node states the precise horn and boundary lifting characterizations. The adjunction translates each lifting square, and the ground model lifting axioms solve it. Fibrancy of Y is invoked exactly to apply this to Y -> terminal. This also proves the stronger map assertion needed later.
5. I read the entire existing lem-coef-brown-split-factorizations statement, not only its title. It gives the split factorizations in both directions with exactly the cofibration/fibration conditions used here. Two-out-of-three supplies each otherwise missing triviality; the intermediate objects are fibrant/cofibrant by composition. Thus no uncited Brown lemma is assumed.
6. The diagonal node states degreewise equivalence implies diagonal equivalence in either direction. The Reedy node supplies degreewise cofibrancy/fibrancy; step 5 supplies the two degreewise invariance assertions. This is also the explicit proof for maps between arbitrary frames, and is not borrowed from a helper that already asserts the item.
7. The Reedy node gives the lifting classes used to compare A with S; both augmentations are weak equivalences, so every comparison component is one. The step checks all stronger hypotheses required by the special-resolution node, which are not part of the definition of an arbitrary frame.
8. The special-resolution node actually concludes diagonal Hom equivalent to the special-zigzag nerve under those exact hypotheses and records index forgetting. The special-hammock node actually concludes that nerve maps weakly equivalently to hammock morphisms. The localization node actually identifies the latter with universal infinity-localization mapping spaces, not merely the ordinary homotopy category. All three are separately cited; the full chain is written.
9. I checked the resolution node's naturality and identity-outer-arrow clause, the reduction node's endpoint actions and normalization, and the localization node's actual-map and composition clauses. These give naturality in the homotopy theory stated in the item; they are not being used to assert an additional strict enrichment. A component contains a vertex, which is an actual X -> Y because degree zero was kept fixed.
10. The Kan node states right properness and the homotopy-pullback replacement description. The pullback used is specifically along the fibration E x_C D' -> D'. I wrote the comparison map rather than assuming strict pullbacks are homotopy pullbacks without the fibration hypothesis. Products use componentwise horn lifts and include the empty product.
11. The Brown node supplies i,p,s with ps=1; preservation of trivial cofibrations plus two-out-of-three proves preservation of weak equivalences only between cofibrants. The Reedy node gives cofibrancy of each frame level; preservation of colimits identifies the latching maps. T was never applied to an arbitrary weak equivalence with noncofibrant endpoints.
12. The Reedy node supplies the two explicit lifts a and b and the relative-latching formulas that T preserves. The source target is replaced by a cofibrant-fibrant Y_c so that every object in the source double-resolution zigzags is cofibrant. This allows T to preserve every displayed weak equivalence. The special-resolution node states the actual index-forgetting diagram comparison and its naturality, so the argument does not use its unstated proof. The hammock-reduction statement supplies the endpoint action; the arbitrary-relative-category localization statement supplies the action of the restricted relative functor on all hammock simplices. The formulas b_n T(i_n)=i'_n r and the maps a^m give the commutative diagrams on which the comparison relies. This repairs the earlier insufficient adjunction/vertex explanation.

For the new statements I tested the smallest cases: the terminal model category, the isomorphism weak-equivalence model on sets, degree zero and degree one of the Reedy construction, constant bisimplicial sets and identity comparison maps. The boundary criterion includes the empty boundary of Delta^0, so cofibrancy is not lost there. The first horn is a vertex inclusion; its image is trivial by the collapse condition and two-out-of-three. In the special-zigzag category I checked that p'a=p, bi=i' and bf=f'a have the required types, that identities give the length-one actual map, and that its vertical maps are indeed weak equivalences. An empty Hom complex is allowed to be Kan and has no components to represent. Finite products include the empty family. Endpoint objects of the general special-resolution helper need no extra hypothesis because its stated special resolutions themselves impose the required replacements. Universe enlargement handles the resolution and diagram categories; no application of a small-index existence theorem to an uncontrolled large category is made.

I checked B's statement-only/self-contained/notation/source/search/blueprint requirements, C's exact statement citations and dependency directions, D's prohibition on moving clauses to renamed children, and E's hypotheses and compatibility formulas. Definition notions are inline or supplied by the cited simplicial-set/Reedy/Kan nodes. I found no source error or statement dispute. The already-existing Brown factorization node is reused; the parent finite-Reedy localization theorem is deliberately not cited back. All new nodes remain unsplit. The delivery preflight, rather than any forbidden library build, is the final mechanical check.

### Continuation check, 2026-10-16

I reopened Hovey Theorem 5.2.5 and the fixed-degree-zero construction in Theorem 5.2.8, the boundary/collapse criterion in Proposition 3.6.8, Low Lemma 1.4, Definition 1.5, Theorem 1.6 and Propositions 3.5-3.7, Hinich Section 1.2 and Theorem 1.3.3, and Cisinski Theorem 3.1.16 and Corollary 3.1.28 online. I checked the retained seven helper statements and the Brown-factorization statement against what each proof step takes from them. The project-source searches again found no frame/hammock theorem to attach, and the current DAG has no duplicate of these seven children. Separate whole-blueprint searches for cosimplicial, Reedy, hammock and bisimplicial returned no matching imported nodes. No SGA route is used.

I repaired one precise C4 risk in step 12: after applying T the augmentation TS -> const(TX) need only be a weak equivalence, so the special-resolution comparison cannot simply be applied to it. The helper now explicitly states the general diagonal/Grothendieck comparison, which is the first part of Low's proof and has no model or resolution hypotheses. Its special index-forgetting equivalence still has every original stronger hypothesis. The step uses the general clause for the intermediate diagram E = Hom(TS,B'), and uses the special equivalence only at the two special endpoints. I wrote the span D -> E <- D' with formulas b T(h) and h' a, checked its variance, cited the bisimplicial-diagonal theorem for the right arrow, and gave both commutative hammock comparisons. The equations p' a = T(p) and b T(i) = i' r check the outer arrows. This supplies the action on all simplices, with no assertion that T preserves trivial fibrations. I regenerated every quotation from the resulting node statements.

The new helper clause was searched with the prescribed msearch command in addition to the retained execution-log-backed searches. The grep hits concern Grothendieck topologies, not the diagonal or Thomason equivalence. The semantic hits concern products of ordinary nerves and the 2-truncated homotopy-category API; none states the added comparison. As a small-case check, constant P and Q give a constant Hom bisimplicial set, while I has the same Hom components and contractible Delta/Delta-op indexing factors. Identity T, a and b reduce the written span to identities. Empty Hom and the zero/one degrees remain allowed. No item statement, hypothesis, unit, chapter, or maintainer field was changed.

## Validation

The required command `python3 /home/ubuntu/weil-launcher-nt/deliver.py NI lem-coef-cosimplicial-frame-mapping --no-push` returned `OK (not pushed)` with the maintainer preflight passed. After making the comparison index category explicit, the same command was rerun for the final sandbox. An independent read-only overlay check found every referenced node, no reachable dependency cycle, exact proof_deps/uses agreement, twenty-one valid verbatim citations, and seven statement-only new nodes. No delivery was pushed.

## Second reading by NI

I reopened the item and all seven statement-only children, checked the cited Hovey, Cisinski, Low/Dwyer–Kan, and Hinich passages, and reran the repository-wide duplicate and blueprint searches. I tested the zero/one degrees of the Reedy construction, the terminal and isomorphism model categories, constant bisimplicial sets, identity functors, empty products, and empty mapping complexes. No statement or hypothesis requires correction.

- Step 1: checked the two functorial factorizations and localization representatives against the model-category axioms; verdict: elementary and complete.
- Step 2: checked the fixed-degree-zero Reedy induction, latching formula, and dual fibrant construction against Hovey Theorem 5.2.8; verdict: hypotheses and degree-zero edge case are correct.
- Step 3: checked the coend adjunction, boundary identification, and collapse argument against the cited cellular criterion; verdict: all uses are stated by the child node.
- Step 4: checked horn and boundary adjoint lifting and the fibrant-target specialization against the Kan characterization; verdict: elementary and correctly scoped.
- Step 5: checked both Brown factorizations, retractions, and two-out-of-three arguments; verdict: elementary once the cited split-factorization node is opened.
- Step 6: checked both bisimplicial directions, objectwise cofibrancy, and frame-map invariance against the diagonal child and Reedy child; verdict: complete and non-circular.
- Step 7: checked the relative latching maps of the map from the coproduct frame and the Reedy lift; verdict: elementary with the cited Reedy formulas.
- Step 8: checked the special-resolution hypotheses and the three comparisons through the special hammock and universal localization nodes; verdict: each comparison is separately cited.
- Step 9: checked endpoint actions, naturality, composition homotopies, and degree-zero normalization against all three cited comparison nodes; verdict: no hidden vertex-only argument remains.
- Step 10: checked the pullback factorization, right-properness application, finite products, and the empty-product case; verdict: elementary and correctly assumes only a Kan fibration.
- Step 11: checked Brown preservation only for cofibrant endpoints, latching-colimit transport, and the derived functor construction; verdict: no arbitrary-endpoint preservation is used.
- Step 12: checked the cofibrant-fibrant target replacement, prescribed Reedy lifts, variance of the bisimplicial span, and the hammock action on all simplices; verdict: the comparison uses the general index-category clause and does not assume preservation of trivial fibrations.
- `lem-coef-reedy-model-structure`: checked self-contained model/Reedy definitions, both latching and matching formulas, Delta and opposite-Delta cases, and degree-zero extensions; verdict: retained statement is accurate.
- `lem-coef-simplicial-boundary-collapse-test`: checked boundary generation, horn filtration, arbitrary weak-equivalence preservation for simplicial sets, and the adjoint Quillen conclusion; verdict: retained statement is accurate.
- `lem-coef-kan-quillen-right-proper`: checked generating boundary/horn characterizations, Kan fibrancy, right properness, and homotopy-pullback replacement; verdict: retained statement is accurate.
- `lem-coef-bisimplicial-diagonal-equivalence`: checked both row/column forms and the homotopically constant specialization on constant and degree-zero cases; verdict: retained statement is accurate.
- `lem-coef-special-resolution-zigzag-nerve`: checked the variance equation in `I(P,Q)`, the functor to the three-arrow category, identity degree-zero object, and hypothesis-free general comparison; verdict: retained statement is accurate.
- `lem-coef-special-hammock-reduction`: checked the commutative-diagram equations, two-out-of-three for vertical maps, endpoint pullback/pushout actions, and identity zigzag; verdict: retained statement is accurate.
- `lem-coef-hammock-infinity-localization`: checked the hammock conventions, fibrant replacement, universal property, actual-map normalization, and functoriality; verdict: retained statement is accurate.

No node was removed: every child is a genuine external technical input and no existing DAG node states the same result. No node statement, source, hypothesis, or proof step needed repair. I changed only this second-reading record, preserving the worker's review and all citation/search records.
