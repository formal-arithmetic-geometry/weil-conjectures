# Q47 — lem-coef-simplicial-right-fibration-presentation

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-right-fibration-presentation.json`: statement, split into 13 proof steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-unstraightening-external-products.json`: new statement-only lemma; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-enriched-right-quillen-equivalence.json`: new statement-only lemma; no Mathlib match.
- `citations.json`: one verbatim statement quote for each of the 25 step/node citations.

## Attachments

None. Searches by the parent blueprint tag, the proposed child IDs, unstraightening/straightening and right-fibration terminology found no project declaration in `WeilConjectures/` in slopmaster2 that proves this item. The upstream master checkout is reference material, not evidence of a closed proof. No Mathlib declaration was treated as a project attachment.

## Literature requested

WANTED: Lurie, Higher Topos Theory, Sections 2.1.4 and 2.2.1–2.2.3, especially Theorem 2.2.1.2, Proposition 2.2.1.1, Remarks 2.2.2.11–12, Lemmas 2.2.3.4 and 2.2.3.6, and Corollaries 2.2.3.12–13, for lem-coef-simplicial-right-fibration-presentation.

WANTED: Lurie, Higher Topos Theory, Remark 2.2.2.12, printed p.78, for lem-coef-unstraightening-external-products.

WANTED: Lurie, Higher Topos Theory, Remark A.3.1.9 and Proposition A.3.1.10, printed pp.854–856, and Proposition A.3.3.2, for lem-coef-enriched-right-quillen-equivalence and lem-coef-simplicial-right-fibration-presentation.

Read these places online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; no document was downloaded or written to the shared repository. These are simplicial homotopy theory results, not Stacks theorems; there is no Stacks tag to invent. No SGA source is used. The proof is marked agent-written because the archival source is not in the local literature collection.

## Findings and repairs

The imported item has no proof, and its bundled statement survives the checks below unchanged. Its ordinary Quillen-equivalence clause is already a specialization of the existing, more general `lem-coef-unmarked-straightening-quillen`, and the ordinary slice model is already `lem-coef-contravariant-slice-model`. Neither is recreated. The existing latter statement does not assert the simplicial model structure or mapping-test definition of equivalence: those are proved in steps 3–6, rather than attributed to that node.

The fiber of the explicit cone unstraightening is `Sing_Q F(s)`, not literally `F(s)`. Steps 8–10 use the actual pinched resolution and construct the natural weak equivalence. Enriched Yoneda for a representable cannot replace this calculation. Also the ordinary Quillen theorem alone does not identify the particular enrichment of U as a Dwyer–Kan equivalence. The external-product child supplies the action on simplices; the generic enriched right Quillen criterion then applies to that action.

The generic criterion records only the simplicial-set consequence of HTT A.3.1.9–10. It requires every object of the source of the left adjoint to be cofibrant, and assumes the right adjoint has the given simplicial enrichment. It does not assume that the cone left adjoint is enriched, or that the ordinary adjunction is an enriched adjunction. The more general tensor-comparison notation from HTT is unnecessary in its statement.

I corrected the proof route for opposites: the transported adjunction is ordinary, and the covariant simplicial model axiom follows by the explicit pushout-product argument with the parameter also reversed. No assertion that the opposite operation is a simplicial functor is needed. Likewise, the comparison between a Kan complex and its opposite is an equivalence of spaces, via geometric realization, not an invented natural simplicial map between them.

The unit/chapter and current main-20261015 blueprint ancestor were read. This technical branch serves the first and last derived R Hom / inverse-limit comparisons in paragraph 2 of `prop-coef-integral-exceptional-adjoint`. It changes no unit-level geometric argument. The parent is not the unit's key node, so no unit record is changed. The only off-unit proof citation is the generic right-fibration-over-Kan lifting theorem, explicitly declared in `split_report.tool_uses`.

## Not duplicates

lem-coef-unstraightening-external-products vs lem-coef-unmarked-straightening-quillen: the existing node gives the cone adjunction, Quillen equivalence and the point-fiber formula; it does not give external products over two independent bases or the tensor/product formula for arbitrary diagrams. This missing product input constructs the enrichment and constant-product map in the parent.

lem-coef-unstraightening-external-products vs lem-coef-pinched-rigidification-resolution: the existing node gives the Q coend/singular adjunction and its weak comparisons; it does not identify unstraightening of an external product with the product over two bases.

lem-coef-unstraightening-external-products vs lem-coef-enriched-category-tensor-calculus: the existing node concerns coherent enriched infinity categories and their closed tensor/cotensor structures, not strict cone unstraightening of simplicial diagrams or its strict external-product isomorphism.

lem-coef-enriched-right-quillen-equivalence vs lem-coef-model-infinity-derived-adjunction: the existing node constructs an ordinary derived adjunction; it does not assert that the given enrichment of a right Quillen equivalence induces weak equivalences on the actual bifibrant mapping simplicial sets.

lem-coef-enriched-right-quillen-equivalence vs lem-coef-simplicial-model-nerve-localization: the existing node identifies one model category's bifibrant nerve and mapping spaces with its localization; it does not identify the actual mapping-space action of an arbitrary enriched ordinary right Quillen functor with that derived comparison.

lem-coef-enriched-right-quillen-equivalence vs lem-coef-simplicial-projective-model-calculus: the existing node supplies projective model structures and enriched index-change Quillen equivalences; the new criterion applies to an ordinary adjunction where the left adjoint need not be enriched and is not an index-change functor.

The exact new IDs, relevant phrases, HTT Remark 2.2.2.12 and A.3.1.9–10 were searched in the DAG; there was no existing node stating either child. Whole-blueprint searches for external-product unstraightening and enriched right Quillen equivalence found no blueprint match. The item and children therefore have `same_as: []` and their inherited blueprint ancestry is retained.

## Mathlib search review

Every recorded new search was actually run through msearch.py with group Q47 and this parent item. The raw returned results are retained in the node entries, with the exact tool/query. Each child has LeanFinder, Loogle, source grep and LeanSearch, and a second semantic phrasing. The parent retains its inherited searches and adds this worker's searches. No unavailable service has been called a negative result.

For external products I read the hits concerning ordinary monoidal external-product composition, enriched products, simplicial-object enrichment, augmented-simplex tensor, ordinary nerves and Dold–Kan. They have different objects and no cone unstraightening. The source grep has no unstraightening or Sing_Q declaration. For the generic criterion I read the bifibrant-object and localization/homotopy-class hits, ordinary adjunction/fully-faithful statements, model Quillen injective-resolution results, and the simplicial-category basic definitions. These do not assert the needed action on mapping simplicial sets. The only relevant source grep lines in SingularSet.lean are a TODO about a Quillen equivalence; they are not a theorem. For the parent the all-horn Kan-model fibration hits do not present one-sided fibrations. Neither new statement is an exact Mathlib theorem or a one-line specialization of the hits.

## Review by Q47

I read HTT Section 2.2.1 for the actual cone adjunction, the point-base Q calculation and Remarks 2.2.2.11–12 for the fiber/product/enrichment formulas, Lemmas 2.2.3.4 and 2.2.3.6 for mapping and fiberwise equivalences, the contravariant model discussion and opposite remark, and Appendix A.3.1.9–10 for the enriched right Quillen criterion. For each new node I checked precisely that its hypotheses are those used there: the product statement is valid for arbitrary simplicial diagrams and bases, and the generic criterion is specifically over Kan-model simplicial sets with all source objects cofibrant. No source calls an arbitrary base a quasicategory here. I also read the exact statements of every node used below, not their proofs as a substitute for their statements.

Step 1 uses the first paragraph of `lem-coef-simplicial-presheaf-projective-model` only for the Cartesian combinatorial simplicial Kan model. Its ordinary-index presheaf clause is not misapplied to an enriched index. The actual enriched projective structure and enriched end come from `lem-coef-simplicial-projective-model-calculus`, which explicitly allows a small simplicial index without local Kan hypotheses.

Step 2 uses `lem-coef-contravariant-slice-model` for the ordinary model, right-anodyne trivial cofibrations, fibrant objects and all-monic cofibrations. It uses `lem-coef-unmarked-straightening-quillen` with the identity index map for the precise cone formula and ordinary Quillen equivalence. The identity is a Dwyer–Kan equivalence on the nose. There is no dependence here on the parent theorem itself.

Step 3 uses the actual right-anodyne pushout-product statement to construct the product frame, with the elementary last-vertex horn filtration written out. The model node says right-anodyne maps are trivial cofibrations. The frame node requires no enrichment and therefore supplies Kan mapping complexes and localized mapping spaces before the slice simplicial model is proved. The augmentation is objectwise weak, the degree-zero map is the identity, and all latching maps are monic. This avoids circular use of SM7.

Step 4 uses that frame comparison and its representation of every localized object by a fibrant one. It writes the two equations establishing invertibility from bijectivity of precomposition. `lem-coef-model-localization-detects-weak-equivalences` explicitly permits nonfibrant objects, which matters here. Passing to the homotopy category of the coherent localization gives the ordinary localization, so its reflection statement applies. This establishes the parent's mapping-test definition, absent from the ordinary slice-model statement.

Step 5 takes only the pushout-product assertion from the right-anodyne node and the all-horn conclusion from `lem-cbc-right-fibration-space-fiber`. The latter requires a Kan base; that base is the mapping complex already proved Kan in step 3. Lifting against the saturated right-anodyne class is explained by pushout, sequential lifting and retracts. The off-unit node is a generic homotopy-theory tool, not a purity route.

Step 6 uses the Kan-model simplicial axiom of the cited presheaf-model node, then transposes lifts explicitly. Both inputs to its Kan SM7 application have the required type: one is a simplicial-set monomorphism and the other the Kan restriction fibration of step 5. Triviality when either input is weak is what step 4 tests. The cotensor is specified over S, so the enrichment is that of the slice rather than the ambient functor complex.

Step 7 now may use `lem-coef-simplicial-model-nerve-localization`, as the slice has been proved simplicial. It compares actual mapping spaces and composition, not just objects. The detection node supplies the reverse implication from homotopy inverse, and the ordinary slice-model node supplies precisely the fiber criterion for fibrant objects. The short Kan-horn argument explains why a component equation supplies a single simplicial homotopy.

Step 8 uses only the first part of `lem-coef-pinched-rigidification-resolution`: the coend adjunction, natural weak p_K and weak evaluation for Kan targets. `lem-coef-pinched-cube-latching` gives the latching monomorphisms and weak contractibility needed for the frame theorem. I do not assume Sing_Q is simplicially equal to the identity. Both two-out-of-three calculations are written, including the naturality square needed to reflect the weak equivalence from its Q realization. The map eta is defined for every simplicial set; its weak-equivalence claim is made only for Kan ones.

Step 9 uses the external-product child to construct U's action on simplices, including the product and unit compatibility, before using the enriched criterion child. The latter's cofibrancy hypothesis is satisfied on the slice side; its projective and slice model hypotheses were established in steps 1 and 6. It therefore applies to the actual enrichment just constructed, not to an unspecified derived functor.

Step 10 quotes the exact Sing_Q fiber formula in the general unmarked theorem, then uses step 8 for the comparison. The external-product child is used with the point and terminal diagram; U of the terminal diagram is S by the unique natural transformation formula. The constant-product map is thus an actual map with the specified direction, and only its fiberwise property is claimed.

Step 11 uses the cone formula in `lem-coef-unmarked-straightening-quillen`; base change is proved by the pushout universal property, with the category representing a diagram explicitly described. The simplex bijections commute with operators, and composition is equality of successive restrictions, not a vague coherence claim. The universe argument concerns each object and each construction, not the large category of all small objects. This is elementary from the stated cone construction.

Step 12 uses the subset-poset definition in `lem-coef-coherent-nerve-comparison`. Reversal preserves union and changes the simplex operators in exactly the stated way. The coordinate-reversal formula proves the realization homeomorphism, so preservation of weak homotopy equivalences is justified. Both the parameter and the slice object are reversed for pushout products and mapping complexes. This proves the covariant simplicial structure without falsely identifying opposite with an enriched functor.

Step 13 uses `lem-coef-model-infinity-derived-adjunction`, which explicitly requires only an ordinary Quillen adjunction and gives coherent right-derived functors and preservation of weak equivalences on fibrant objects. Projectively fibrant here means objectwise Kan. The fiber comparison is an equivalence of spaces using reversal, and the constant product has X opposite, exactly as in the item's statement. Base-change compatibility is inherited from the actual isomorphisms of step 11.

For B1–B10, both new nodes have statements only, all objects and hypotheses introduced, actual searches with raw results, precise non-Stacks source places, complete blueprint ancestry and no Lean attachment. For C1–C8 I read every cited statement and supplied exact quotations, kept only the clauses they actually say, checked the dependency closure for cycles, and declared the sole off-unit tool. For D1–D5 the two new statements are generic inputs rather than restated clauses of this item: the proof itself constructs the enrichment, frame/simplicial structure, comparisons, base change and duality. For E1–E7 I checked the needed fibrancy and cofibrancy at each application and used no properness, connectedness or nonempty-base assumption.

Small cases: for an empty base both diagram and slice constructions are terminal and U has empty total space; the fiber conditions are vacuous. For the point the fiber is Sing_Q, with Q^0 a point, consistent with all formulas and with the empty Kan complex. In the external-product child an empty base gives an empty total product, K empty gives the empty unstraightening, and K terminal gives the unit isomorphism. Its two independent diagrams do not require cofibrancy or Kan values. In the generic criterion the identity Quillen adjunction gives the identity Dwyer–Kan equivalence; the terminal model category and empty mapping components create no extra nonemptiness requirement. These tests do not suggest a statement dispute. No statement was weakened.

## Unfinished work

Stage 1 only: the two new supporting statements remain intentionally unsplit for subsequent workers. No Lean was written or compiled. The required dry run is the final validation; this delivery is left for a second reader and is not pushed by this worker.

## Second reading by Q47

- Item statement: checked every clause against HTT Section 2.2.1, Theorem 2.2.1.2, Proposition 2.2.1.1, Proposition 2.2.3.11, Lemmas 2.2.3.4 and 2.2.3.6, Remarks 2.2.2.11–12, Proposition A.3.3.2, and the opposite-base dual; verdict: unchanged and edge cases (empty base, point, terminal and empty diagrams) are consistent.
- Node `lem-coef-unstraightening-external-products`: checked arbitrary bases, diagrams, products, the `Q`-singular specialization, units, and empty inputs against HTT Remark 2.2.2.12; verdict: self-contained statement-only generic input, no duplicate or Mathlib match.
- Node `lem-coef-enriched-right-quillen-equivalence`: checked the all-cofibrant source hypothesis, ordinary Quillen equivalence, given simplicial right-adjoint enrichment, and bifibrant Dwyer–Kan conclusion against HTT Remark A.3.1.9 and Proposition A.3.1.10; verdict: self-contained statement-only generic input, no duplicate or Mathlib match.
- Steps 1–2: checked the cited projective-model, slice-model, and unmarked-straightening statements; verdict: each citation supplies the asserted model structures, cone adjunction, fibers, and ordinary Quillen equivalence.
- Steps 3–4: checked the latching/frame calculation, right-anodyne last-vertex filtration, localized mapping comparison, and converse detection; verdict: dependencies state the needed frame and localization facts, with the finite horn argument written explicitly.
- Steps 5–7: checked pushout-product lifting, Kan-base restriction, SM7 transposition, and the right-fibration mapping/homotopy criterion; verdict: hypotheses are in force and no fibrancy or nonemptiness assumption is omitted.
- Steps 8–10: checked the `Q`-frame comparison, external-product action, enriched composition, fiber formula, objectwise weak-equivalence preservation, and constant-product map; verdict: uses the actual `Sing_Q` fiber and writes both two-out-of-three arguments.
- Steps 11–13: checked cone-pushout base change, size bookkeeping, opposite transport, covariant fibers, and derived-functor computation; verdict: ordinary opposite transport is used without assuming an enriched opposite functor, and all claimed compatibilities follow.
- Citations: checked every quote in `citations.json` verbatim against the cited node files; verdict: quotes match and dependency closure is acyclic.

Changes made: restored the parent node's overwritten `created` metadata to Q47, restored its Q47 blueprint ancestry, marked the parent split, and added the missing source places for the two generic inputs to the parent source record. No mathematical statement or proof step was otherwise changed.
