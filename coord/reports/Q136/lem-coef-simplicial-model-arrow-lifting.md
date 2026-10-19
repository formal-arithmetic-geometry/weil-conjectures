1. Files written:

- `dag/nodes/sec-six-functors/lem-coef-simplicial-model-arrow-lifting.json` — statement split into four proof steps; statement unchanged; existing Mathlib searches retained.
- `citations.json` — one verbatim statement excerpt for every node used in each step.
- No new nodes and no Mathlib leaves. The earlier sandbox candidate `lem-coef-infinity-pullback-mapping-spaces` was removed before delivery because the existing `lem-coef-accessible-pullback-filtered-colimit` states its mapping-space formula.

2. Attachments: none. The project-source search for the item tag, the proposed supporting-node tag and Kan/arrow representation found no declaration stating the item. The upstream master reference is not evidence of a completed proof.

3. WANTED: local archives of Gepner–Haugseng, *Enriched infinity-categories via nonsymmetric infinity-operads*, Theorem 5.3.17; Hovey, *Model Categories*, Chapter 5; Hinich, *Dwyer–Kan localization revisited*, Section 1.2 and Theorem 1.3.3; HTT, Lemmas 5.4.5.4–5.4.5.7; and Kerodon Tag 01DK. These are reference requests, not unperformed Mathlib searches. The cited DAG statements are the interfaces used by the proof. The online Gepner–Haugseng proof, HTT 2.4.4.3, Hovey and Hinich PDFs, and Kerodon 01DK were opened during continuation. The proof is marked agent-written because the consequence is assembled here and those documents are not locally archived.

4. Corrections to the earlier attempt: its new mapping-space node duplicated an existing, more general statement (delivery-errors C5). Its use of HTT 2.4.4.3 as a general pullback-mapping-space theorem was inaccurate: that proposition characterizes Cartesian edges for an inner fibration. The repaired proof cites the exact existing pullback statement instead. It also replaces the insufficient coherent-nerve-only justification for the prescribed localization functor j by the model-localization and actual-map clauses of the frame lemma (C1/C4). The final arrow-equivalence conclusion now cites the arrow-morphism-space formula and pointwise-equivalence theorem. No statement correction was necessary.

The blueprint ancestry is retained from the current repository and was confirmed with `blueprint_refs.py ancestor`. The current main-20261015 exceptional-adjoint proof discusses finite reductions and derived limits, not the simplicial-model paragraph claimed by the earlier report. The item is a generated auxiliary node with historical ancestry through enriched completion. Its split supplies its own source-motivated auxiliary assertion; it changes no unit, chapter, target or ancestor node.

5. Nothing remains unfinished mathematically at this one-level split. The server dry run and push are recorded below when they finish.

## Review by Q136

I reread the current repository item and its source entry, the chapter and unit records, the current main-20261015 exceptional-adjoint proof, and the complete statements of all five proof dependencies. Gepner–Haugseng Theorem 5.3.17 explicitly introduces the localization of simplicial sets at weak equivalences and a pullback over spaces. The present arrow-representation lemma is an auxiliary consequence, not a numbered claim of that paper. Its statement was compared byte for byte with the current repository and retained unchanged. No SGA source is used.

Step 1 uses `lem-coef-kan-quillen-right-proper` for the model structure, monomorphism cofibrations and Kan fibrant objects, and `lem-coef-cosimplicial-frame-mapping` for existence of fibrant representatives in its infinity localization. Every object is cofibrant because its initial map is injective. The localization here is the prescribed j, since the hypothesis gives its universal property for exactly the same weak equivalences. This closes the gap in the earlier comparison with the coherent nerve. Universes are enlarged for the ambient categories without enlarging the chosen U-small simplicial sets.

Step 2 again uses the frame node, now its explicit clause that every component between a cofibrant source and fibrant target is represented by an actual map. It applies to K and L from Step 1. The transported component is beta inverse composed with p(F) composed with alpha. I checked the directions: the path retained for Step 3 runs between beta composed with j(f) and p(F) composed with alpha, both maps jK to pB.

Step 3 uses the unconditional mapping-space formula in `lem-coef-accessible-pullback-filtered-colimit`. Its statement explicitly gives the common target Map_C(F(a),G(b prime)) and the two maps e prime composed with F(u) and G(v) composed with e. Substitution gives exactly Map_S(jK,pB) and the two maps written in the step; no accessibility, colimit-preservation, Cartesian-fibration or local-smallness hypothesis is imported from the other clauses. The vertex (f,F,h) provides the required mapping-space component. For the ordinary nerve, a right-pinched simplex is a string of identities followed by a single ordinary morphism, so different ordinary maps cannot be connected there. Thus the f-projection is exact even though the E-projection is only specified up to component.

Step 4 uses `lem-coef-infinity-arrow-morphism-square` to turn the path between r(tilde F) and F, with identity endpoint components, into an arrow-category transformation. `lem-coef-infinity-pointwise-equivalences` makes that transformation an equivalence, because its endpoint components are homotopic to identities. Both statements were opened, and citations.json quotes their actual formulas/criteria. This replaces the earlier unsupported label elementary on the full arrow-equivalence conclusion.

For B1–B9 and D1–D5, there is no new statement to hide a proof, restate a clause or duplicate an interface. I searched the entire current DAG by pullback/mapping-space notions, then read the more general accessible-pullback node that made the proposed new node unnecessary. Whole-blueprint searches for mapping spaces and homotopy pullback returned no imported blueprint node stating this item. The retained search log and item search records were read; no past search was invented, erased or repeated. The removed candidate's searches remain in searches.jsonl as historical evidence.

For E, I checked K empty, L empty, identity F, and p a constant functor to a point. Maps out of the empty complex exist, while a map to an empty complex forces the source empty, so the case split is consistent. When p is constant, the homotopy pullback mapping space reduces to the product expected by the construction. The argument uses neither a Cartesian lift nor a chosen isofibration. Each proposed dependency's complete statement/proof closure was checked for a path back to this item, and none occurred. All four proof steps are shorter than 2000 characters, and the non-elementary parts are precisely the cited statements. The initial required dry run was started before these repairs; its result must finish before another invocation or push.

## Continuation and validation

The prior provider failures did not invalidate the sandbox. On this continuation no active deliver.py invocation for this item existed. The required dry run finished with exit 0 and OK (not pushed) at e394c259b8. I reread all five current proof-dependency statements, the two definition statements, the parent's actual step 6 using this item, and the current blueprint ancestor. The item remains unsplit in the shared repository, its statement is unchanged, and all cited clauses still match. I restored blueprint.from.place to the current repository's more precise historical-ancestry description, removing the earlier sandbox's unsupported assertion that a current blueprint paragraph explicitly contains simplicial models. This metadata correction requires a fresh final dry run before the authorized push. Mathematical repairs and the provenance corrections above supersede the earlier attempt recorded below.

## Earlier attempt (superseded)

The following earlier report is preserved for provenance; its new-node count and proof assessment describe the superseded sandbox, not this delivery.

1. Files written:

- `dag/nodes/sec-six-functors/lem-coef-simplicial-model-arrow-lifting.json` — statement node split; no new Mathlib leaf.
- `dag/nodes/sec-six-functors/lem-coef-infinity-pullback-mapping-spaces.json` — statement-only supporting node; Mathlib searches found no match.
- `citations.json` — verbatim citations for every non-elementary step use.

2. Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id and its notions; no sorry-free declaration states the item.

3. WANTED: an archived local copy of HTT, especially Propositions 1.1.5.10, 1.2.5.1 and 2.4.4.3, for the new supporting node and the arrow-representation proof. The online source was read.

4. No statement or source error was found. The imported item had an empty proof and was retained verbatim. I found no duplicate node in the DAG or current blueprint. The new node is strictly a mapping-space calculation used by the item and does not restate the item's arrow-lifting conclusion. After the initial dry run, I reran the required `msearch.py` searches using the supporting node id and recorded those exact queries and hits; I also corrected that node's `created.item` metadata to this Q136 item.

## Review by Q136

I read the item source entry (Gepner–Haugseng, Theorem 5.3.17 context) and the HTT references named in the item. I also read the complete statements of `def-coef-infinity-category-of-spaces`, `lem-coef-coherent-nerve-comparison`, and the new `lem-coef-infinity-pullback-mapping-spaces`. Step 1 uses the definition's assertion that the infinity category of spaces is the coherent nerve of small Kan complexes, and the coherent-nerve node's mapping-space equivalence; these give Kan endpoint representatives and an actual simplicial map representing the arrow component. Step 2 uses exactly the new node's homotopy-pullback mapping-space formula, including its path coordinate and natural coherent composition, to combine the actual simplicial map with the chosen arrow in `E`. Step 3 is the elementary translation from a mapping-space point to an arrow in the coherent arrow category; it uses no uncited theorem. I checked that the universes are nested as required, that empty Kan complexes are allowed, and that no Cartesian-fibration assumption is introduced. The new node introduces both functors `u` and `v`, both endpoint equivalences, and all objects in its statement; it is statement-only and carries searches of LeanFinder, Loogle, grep and LeanSearch, all with no match. I corrected the supporting statement to make the functors and endpoint equivalences explicit before writing the citations. I then checked the supporting node metadata and search provenance against the dry-run diagnostics, corrected its `created.item`, and replaced its search records with the exact four searches actually run. No SGA source is used.

5. Nothing remains unfinished in the split itself; the required server dry run is the next validation step.
