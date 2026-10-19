# Stage-1 report: lem-coef-kan-diagram-localized-evaluation

## Files written

- `dag/nodes/sec-six-functors/lem-coef-kan-diagram-localized-evaluation.json`: statement node, now split into six proof steps; no Mathlib match. Its statement, source, five statement dependencies and ancestry are retained. Existing searches are retained and five actual searches from this sandbox log are appended.
- `citations.json`: one verbatim statement extract for every step/node citation, checked against the shared DAG. Some extracts include adjoining material so that each remains one contiguous quotation.
- `report.md`: this report.

## New nodes

None. There are zero new nodes and zero new Mathlib leaves. The argument is a deduction from existing localization, rectification, and pointwise-equivalence statements. The explicit chain calculation is elementary and stays in the item, rather than becoming another node.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint id and for enriched evaluation, rectification, objectwise Kan and coherent nerve. There was no declaration stating this item. Also checked `dag/lean_names_upstream.json` and the read-only upstream master for these terms; upstream sorry declarations are not proof evidence.

## WANTED

WANTED: archival Lurie, Higher Topos Theory, Section 1.1.5, Proposition 4.2.4.4, Remark 4.2.4.5, Example A.3.2.18 and Proposition A.3.3.2, for this item.

WANTED: archival Lurie, Higher Algebra, Theorem 1.3.4.20 and Remark 1.3.4.16, for this item.

WANTED: archival Kerodon, Subsection 4.4.4, Theorem 4.4.4.4 (01DK), for this item.

These are absent from the local literature inventory. I read the HTT and HA primary PDFs online; the Kerodon individual theorem page did not expose its mathematical body, so I opened the containing subsection 01DF. No source was downloaded or written into the project. The deduction itself is marked `proof_origin.by = agent`, with the recorded blueprint ancestor as its local source. No Stacks tag states these infinity-categorical comparison theorems; no SGA source is used.

## Problems found and corrections

The assigned node was an unsplit statement, with no proof or Lean audit recording an existing declaration. I found no false clause or missing hypothesis and made no statement change. A proof merely applying rectification to the objectwise Kan subcategory would be invalid: projectively fibrant need not mean projectively cofibrant. Steps 4 and 5 instead compare the actual evaluation functor with rectification on the bifibrant subcategory, then use the localization theorem for the fibrant and bifibrant inclusions. This identifies the specified evaluation, rather than just constructing an unrelated equivalence between the two infinity categories.

The diagrams are covariant on `C[K]`; I checked the covariant projective paragraph of the presentation node, rather than silently using its contravariant `D_S`. No local Kan condition is imposed on `C[K]`, no quasicategory condition is imposed on K, and no simplicial enrichment of a functorial replacement is assumed.

## Blueprint and duplicate searches

Read the chapter record `sec-six-functors`, unit record `sk-prop-sf-biduality-general`, and paragraph 2 of `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. The item is a generic coherent-diagram tool below that coefficient-adjunction paragraph; it changes neither the unit statement nor its route or realization fields. Its existing `blueprint.from.place` is specific and retained. `blueprint_refs.py ancestor` returned `prop-coef-integral-exceptional-adjoint` as recorded. Whole-blueprint searches for `localization`, `rectification`, `pointwise equivalences`, `Kan`, and `enriched` revealed no blueprint statement equivalent to this item; `same_as` remains empty. Whole-DAG statement searches found the existing pointwise-equivalence and simplicial-model inputs used here, so no duplicates were created.

## Not duplicates

No new nodes; no new/existing pairs require differentiation.

## Mathlib searches

Read all five new search results in `searches.jsonl`: LeanFinder with two different phrasings, Loogle for `"SimplicialNerve"`, grep for `rectif|coherent.*diagram|diagram.*localiz|localiz.*diagram` in `AlgebraicTopology`, and LeanSearch for projective-model localization presenting space-valued functors. All five services returned successfully. Hits concerned the definition of the coherent nerve, strict-category localizations, the ordinary homotopy-category nerve adjunction, strict Segal sets or enrichment of simplicial objects. None stated this equivalence of infinity categories. Read `Mathlib/AlgebraicTopology/SimplicialNerve.lean`: its introduction explicitly leaves the locally Kan quasicategory assertion and the Kan-complex infinity category as future work. That definition is useful infrastructure, not an exact or one-line theorem matching this item. Every appended search is copied from the command's actual log; inherited searches are untouched.

## Review by NE

I reviewed the split against delivery-errors B through E with the node statements open. The source for the item was HTT 4.2.4.4 and its projective-model remark, combined with HA 1.3.4.20 and the explicit fibrant/bifibrant variants in 1.3.4.16. The local blueprint paragraph explains why a comparison retaining all Hom-diagram coherence is needed, but does not itself prove these general foundations. Scholze Lecture II, printed pp.13–15, was read locally for the quasicategory, Kan-complex and functor-category conventions. There are no new nodes needing separate source reviews.

For step 1 I checked that `lem-coef-simplicial-presheaf-projective-model` expressly asserts that the Kan structure is combinatorial and simplicial, beyond what `lem-coef-kan-quillen-right-proper` alone says. The latter supplies monomorphism cofibrations and Kan fibrant objects, so all simplicial sets are cofibrant. The model-nerve localization node identifies the resulting Kan-complex nerve with spaces. The right-fibration presentation node expressly supplies the covariant simplicial projective model on `C[K]`, with objectwise fibrations/weak equivalences. The coherent-nerve comparison supplies the locally Kan nerve assertion. The enhanced-functor-cone-calculus node supplies closure of Fun(K,C) under quasicategories for arbitrary K. This last node is an off-unit generic tool, declared in `split_report.tool_uses`, rather than a replacement for a unit argument.

For step 2 I checked the coherent-nerve adjunction and its ordinary-category restriction against that node's statement. Right-adjoint preservation of products follows directly by adjunction and the product universal property. The enriched chain formula writes down the action on a mapping simplex; naturality is exactly the equation needed for composition. Faces and degeneracies are precomposition by monotone maps. These are elementary constructions from the cited definitions; they do not hide a separate theorem.

For step 3 I checked that the model-localization statement's comparison agrees with the canonical bifibrant inclusion, so the actual edge a(k), not an arbitrarily chosen edge between its endpoints, is inverted. `lem-coef-infinity-pointwise-equivalences` explicitly allows arbitrary simplicial K and detects equivalence of the whole transformation. Thus the step is stronger than a list of vertex comparisons and uses precisely that node's statement.

For step 4 I checked all hypotheses of `lem-coef-enriched-diagram-rectification`: sSet has the combinatorial simplicial model structure; the small enriched index is C[K]; its identity is a DK equivalence; a projective model is supplied; the theorem explicitly imposes no local Kan hypothesis on the target index. Its stated full-chunk convention allows the value category after universe enlargement. I do not claim that V-small simplicial sets have colimits indexed by larger-universe sets. The canonical ordinary-to-coherent nerve map is the inclusion of constant mapping simplices. The product evaluation calculation identifies its composite with Phi on every ordinary chain, not only on objects. This is a direct restriction of the two formulas, with no independent comparison theorem being hidden.

For step 5 I checked that the model-localization node states equivalence for inclusions of both fibrant and bifibrant ordinary subcategories, and the universal property at the level of full functor infinity categories. Those clauses justify j and lambda and the descent of the equality from step 4. Full faithfulness gives the required equivalence of functors after localization. The displayed quasi-inverse proves E is an equivalence and records its restriction to rectification. No separate lemma simply restating the item's conclusion was introduced.

For step 6 I checked that cofibrant replacement factors the initial map by a cofibration and a trivial fibration in the projective model. Since its target is fibrant, successive lifting shows its source is fibrant too. Objectwise weak-equivalence inversion then is exactly step 3. This final step is elementary given the existing model axioms and the preceding argument.

Small cases checked: K empty gives one empty strict diagram and a terminal coherent diagram category; no vertex is needed in the pointwise criterion. K a point reduces to localization of Kan complexes. K = Delta^1 allows genuinely noninvertible structure maps, so the proof does not accidentally restrict to local systems. The empty Kan complex is allowed throughout; Delta^0 cofibrancy and the component argument add no nonemptiness hypothesis. Arbitrary K is covered by u = identity, so there is no missing fibrant-index replacement. I checked the chosen dependencies have no path back to this item through current statement/proof edges. All six steps are below 2000 characters.

No unfinished mathematical work remains in this one-level split. The existing input nodes remain separate DAG obligations.

## Validation and delivery

The required `deliver.py NE lem-coef-kan-diagram-localized-evaluation --no-push` completed with exit 0 and `OK (not pushed)` at `072a704e54`: server preflight passed, including its DAG and split checks. The earlier standalone `srvcheck.py ... check_dag` session was lost during the provider interruption; no success is claimed for it. The full delivery preflight supplies the completed validation. The push invocation repeats preflight on the packaged report and item before publishing. No Lean compiler or build tool was run.
