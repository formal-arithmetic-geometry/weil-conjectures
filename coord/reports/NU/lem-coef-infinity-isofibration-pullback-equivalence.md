## Worker report

Item: lem-coef-infinity-isofibration-pullback-equivalence. Group: NU. Stage 1 only, direct delivery. Date: 2026-10-17.

### Files written

- dag/nodes/sec-six-functors/lem-coef-infinity-isofibration-pullback-equivalence.json: unchanged statement and statement dependencies; eight complete proof steps, exact dependency union, agent proof origin, split report and recorded Mathlib searches.
- citations.json: one entry for every step/node pair, with a verbatim relevant paragraph or full statement of the cited node.
- report.md: this report.

No new nodes; zero new Mathlib leaves. The search log and preparation script remain sandbox-only supporting files. No unit, chapter, other node, Lean, project tool or live launcher was changed. No git command, Lean command, compiler or Lake command was run in either read-only source checkout or the shared repository.

### Attachments

None. Searched the whole slopmaster2 WeilConjectures tree for the exact `(blueprint: lem-coef-infinity-isofibration-pullback-equivalence)` tag, `isofibration`, quasicategory spellings and both orders of pullback/equivalence. The tag and quasicategory/isofibration notions have no project declaration. Pullback/equivalence hits concern sheaves, automorphisms and topological invariance, not strict pullbacks of quasicategories. Master CategoryTheory was also searched as reference material, without treating sorry declarations there as completed proofs.

### Literature and route

Read the chapter record sec-six-functors, the unit record sk-prop-sf-biduality-general, and the current ancestry proof paragraph 2 in literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md. The unit has no individual proof steps to rebind and this is not its key statement. The auxiliary theorem serves the coherent coefficient tensor/presheaf foundation recorded in the item's inherited ancestry. No chapter, unit, blueprint statement, or statement of this item changes.

The direct theorem source is [Kerodon Corollary 4.5.3.34, Tag 03PM](https://kerodon.net/tag/03PM). Specialize its cospans to C -> B <- A and C -> B <- B with vertical arrows id_C, id_B, y and the two left legs pi. Both required isofibration legs are exactly pi; the changing right leg y is unrestricted. I read its statement and proof, which invokes categorical pullback invariance. Also read [Corollary 4.5.3.28, 033R](https://kerodon.net/tag/033R), [Proposition 3.4.0.9, 032B](https://kerodon.net/tag/032B), and [Construction 3.4.0.3, 010B](https://kerodon.net/tag/010B). They supply the cited existing pullback and homotopy-pullback statements. Read Theorem 4.4.4.4 (01DK) for comparison with the explicit whiskering argument. Read Proposition 4.4.3.7 (01EZ) and Proposition 3.1.7.13 (00UB), including their proofs; the browser's requests for these two timed out but direct read-only HTTPS retrieval succeeded, and their contents were read. No source was downloaded into the repository or sandbox.

WANTED: archived Kerodon Subsections 4.4.3, 4.4.4, 4.5.3, Section 3.4 and Proposition 3.1.7.13, for the sources of the cited existing interfaces and this item. These are Kerodon tags, not Stacks tags: no Stacks tag states this quasicategory theorem.

WANTED: archived HTT, Corollary 5.3.5.4, the inherited contextual application for this item. I opened HTT online and located this corollary: it is an Ind-completion generation statement. Thus it is an application context, not a standalone statement of the general pullback theorem. The proof's direct source locators name the Kerodon results above; the inherited source field is retained as contextual provenance.

The proof is marked agent-written because it expands the mapping-core and inverse-detection arguments rather than claiming the blueprint or the online theorem reference itself is a proof. No SGA source is used.

### Searches and reuse

There was no previous item copy, proof, report or search log in this sandbox when the interrupted turn began. Existing inherited searches have been retained. The five new searches were actually run through msearch.py, and their precise tool, query, result summaries, timestamps and digests are recorded in searches.jsonl and appended to mathlib_searches:

1. leanfinder: The pullback of an equivalence of quasicategories along an isofibration is a functor equivalence
2. loogle: "Quasicategory", "pullback"
3. grep: isofibration|CategoricalFibration|modelCategoryJoyal|categoricalEquivalence
4. leansearch: Pullback of a weak equivalence between fibrant objects along a fibration is a weak equivalence
5. leanfinder: Quasicategory equivalence strict pullback along categorical fibration preserves equivalences without right proper Joyal model structure

All services returned successfully. Loogle and grep returned no hits. Semantic hits included CategoricalPullback.functorEquiv, Quillen-model fibrations, QCat.strictBicategory and generic weak-equivalence stability for trivial fibrations. Read pinned Mathlib CategoryTheory/Limits/Shapes/Pullback/Categorical/Basic.lean:306-362, AlgebraicTopology/Quasicategory/StrictBicategory.lean:14-76, and ModelCategory/Instances.lean:35-175. The first is an ordinary categorical pullback, the second constructs a bicategory, and the last requires the weak map itself to be a fibration. Here y has no such hypothesis. None is an exact result or a one-line specialization of this statement. BrownLemma.lean was also read while considering the abstract model argument; it supplies factorizations, not this quasicategory pullback result.

Before choosing dependencies I searched the whole DAG by isofibration, categorical equivalence, cores, Kan homotopy pullbacks, fibrant pullback and right properness. Opened the statements of the candidate isofibration-base-change, degreewise-cartesian-pullback-cat-infinity, simplicial-pullback-equivalence, fibrant-pullback-mapping-invariance and Brown-fibrant-localization nodes. The first has both total projections fibrant over a common base; it does not apply to y. The simplicial-pullback node is for enriched simplicial categories. The simplicial model lemma requires a simplicial model structure, which should not silently be imposed on Joyal's model. The chosen existing core/pullback interfaces apply directly. Whole-blueprint searches via blueprint_refs.py for `pullback equivalence`, `equivalence.*pullback`, `isofibration`, `fibrant` and `core` produced no node with this statement. The item's same_as remains empty. No new lemma is necessary.

## Not duplicates

No new nodes. In particular no child restates the item or one of its clauses, and no elementary comparison or whiskering construction has been promoted to a new node.

## Review by NU

I checked the statement hypothesis by hypothesis against Kerodon 03PM using the specialization above. The categories A, B, C are quasicategories in one containing universe; pi is the sole isofibration assumed. The strict pullback, projection r and strict identity are precisely the specified maps. The theorem does not assert arbitrary right properness of the Joyal model structure. The proof never assumes y is an isofibration. There are no new nodes whose sources, definitions or edge cases need a separate audit.

Step 1 uses the degreewise-pullback convention of def-cbc-enhanced-diagrams-cones and the inner-fibration definition in lem-coef-infinity-isofibration-exponentiation. It fills A first and then lifts the C horn over exactly y(a), so the chosen coordinates satisfy the required equality. The strict identity follows by the pair definition. This is a direct elementary lifting-square argument, not a quoted base-change theorem.

Step 2 uses the actual exponential-corner assertion in lem-coef-infinity-isofibration-exponentiation with empty source and target Q. The identity maps and terminal maps have the lifting conditions explicitly checked in the text. The actual assertion of lem-coef-infinity-core-kan-fibration is that the map on cores is Kan; applying it to the terminal maps gives Kan cores, not merely a definition of a core. All functor objects fit the fixed containing universe. Equivalence preservation by a simplicial map follows by applying it to the inverse edge and both triangles.

Step 3 uses the actual definition of coherent functor equivalence in def-cbc-enhanced-diagrams-cones. It supplies z and both coherent transformations. The displayed whiskering formula is defined on all simplices and operators, and the map on internal Homs sends the inverse and triangle witnesses as well. This elementary construction proves the required fact, instead of citing a definition as if it asserted a functor-category equivalence theorem.

Step 4 uses lem-coef-homotopy-category-triangle-calculus exactly for the represented inverse and the two triangle witnesses of an invertible edge class. For a mixed edge, the displayed triangle in the product has the desired diagonal as long edge; its other edges are a component equivalence and the image of an equivalence under a simplicial map. Thus the whole homotopy, not just its endpoints, lands in the core. The definitions say that a simplex lies there exactly when all its edges are equivalences. With the two actual restricted homotopies in hand, the statement of lem-cbc-simplicial-homotopy-equivalence-weak applies without any fibrancy or connectedness assumption. This is a short coordinate and triangle verification from the cited statements, with no independent hidden lemma.

Step 5 opens and applies the precise statement of lem-coef-kan-homotopy-pullback-invariance. The six spaces are U,G,V and G,G,V, all Kan; the three vertical maps are Y and identities, and both required squares commute strictly. The formula for the resulting weak equivalence is exactly the formula in that node. It retains the V coordinate.

Step 6 uses the statement, not the proof, of lem-coef-infinity-isofibration-pullback-limit. In particular that statement gives the constant-path comparison on all functor cores, and not merely an equivalence of object sets. Its smallness and isofibration hypotheses are our hypotheses. For lem-coef-kan-pullback-path-comparison I checked that id_G is a Kan fibration by the explicit lift, so the assertion applies even though v need not be analyzed separately. The source strict pullback is identified with V by w -> (v(w),w), a coordinate identification. Both exact composite identities are checked by these coordinate formulas. The cited lem-coef-kan-quillen-model-right-proper-core asserts a model structure with precisely the realization weak equivalences; its model axioms supply composition and two-out-of-three, with no Joyal right-properness claim. Thus rho_Q, the actual postcomposition map, is weak.

Step 7 applies exactly the two-sided simplicial Whitehead inverse statement of lem-cbc-kan-whitehead-inverse to rho_C. It needs Kan source and target, proved in Step 2, and a realization weak equivalence, proved in Step 6. Evaluation at id_C supplies an actual functor t and an actual equivalence edge rt -> id_C, rather than just an inverse morphism in an unspecified localization.

Step 8 applies the same Whitehead statement to rho_E, again with its hypotheses checked in Steps 2 and 6. Precomposition of alpha with r sends its inverse triangles to inverse triangles. Applying b_E and evaluating its source homotopy produces the three displayed edges in the correct functor core. Their composite class is invertible. The actual edge/triangle assertions of lem-coef-homotopy-category-triangle-calculus supply an edge and inverse with both witnesses. The resulting two equivalence transformations are exactly what the definition of functor equivalence requires. This explicitly proves inverse detection rather than invoking an uncited general Yoneda principle.

I checked B1-B9 and C1-C8 against the node files: no new node, no proof sketch inside a new statement, no missing objects or definitions, no stale source-tag meaning, no undocumented Mathlib leaf, and each proof citation has the exact assertion used. The proof dependency list is exactly the union of uses. Dependency-closure exploration for every chosen interface avoids the item, so there is no introduced cycle. The two sec-smooth-purity inputs are declared as generic tools in split_report.tool_uses (simplicial homotopy implies realization weak equivalence, and Kan Whitehead), not inserted into maintainer-owned tool_uses. The other proof inputs are in the inherited unit.

For D1-D5, the actual argument stays in the eight steps: we compare the specific two cospans, compute both composites, and construct the inverse functor and its two transformations. No child node moves the conclusion elsewhere. None of the eight steps exceeds 2000 characters (maximum 1217), and each inline comparison is a short coordinate/evaluation calculation from cited statements.

For E1-E6, I checked the mixed-edge triangle direction in Step 4, the orientation of all three cospan comparison maps in Steps 5-6, and the source/target of every edge in Step 8. I tested A=B=C=empty; Q=empty (all functor cores are points); pi=id_B (the projection identifies with y); y=id_B (the projection identifies with id_C); and discrete categories (an equivalence is bijective on objects, so ordinary set pullback is bijective). For nerves of groupoids with a non-surjective-on-objects equivalence y, the proof still uses pi's equivalence lifting through the existing pullback comparison and imposes no surjectivity on y. If C is empty, E is empty and the conclusion still holds. If B is empty, both A and C must be empty. Whitehead explicitly allows disconnected and empty Kan complexes. No hypotheses were added or dropped.

No statement dispute was found. The imported item was unsplit, so the substantive correction is the missing proof, especially coherent inverse detection; the HTT locator was contextual rather than a direct theorem source, and the direct source is identified above. Nothing remains mathematically unfinished at this split level; the existing cited interfaces retain their own stage-1 status and proofs.

### Validation

The prior attempt requested server review_split through srvcheck.py. This continuation began with the required full deliver.py --no-push invocation. The final dry-run result and pushed commit are emitted by the delivery tool; delivery is reported only after its successful exit.

### Continuation audit, 2026-10-17

Retained the interrupted attempt's complete proof, report, citations and five logged searches. Compared the sandbox item with the current shared node: its statement, statement dependencies, source and ancestry still agree; the shared item remains unsplit. Read the current chapter and unit records and the ancestor proof paragraph. Reopened all ten cited node statements, verified every step/node quote against those current statements, and checked that the dependency closure (144 nodes) has no path back to the item. All eight proof steps remain below 2000 characters (maximum 1217). The final inverse construction in Steps 7–8 uses the two actual Whitehead homotopies in the cited statement, with the edge directions composed exactly as written.

Repeated the read-only project declaration check; neither the exact blueprint tag nor the isofibration/quasicategory notions has a declaration in WeilConjectures, and pullback/equivalence hits concern other objects. Read the recorded Mathlib candidates in Categorical/Basic.lean, Quasicategory/StrictBicategory.lean and ModelCategory/Instances.lean; these still do not state the item's theorem. Reused the logged Mathlib searches without inventing or rerunning any queries. Whole-blueprint searches for isofibration and pullback equivalence and the ancestor command agree with the existing metadata. Reopened Kerodon 03PM and 033R online and read 00UB and 01EZ by read-only HTTPS after browser timeouts. The source specialization uses pi on both isofibration legs and y on the unrestricted changing leg. No mathematical correction or statement change was needed; only this continuation and validation record was added.
