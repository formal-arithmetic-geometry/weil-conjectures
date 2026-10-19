# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-relative-cartesian-equivalence-saturation.json`: item, statement unchanged, eight proof steps, status split; Mathlib no exact match after two semantic phrasings and the logged Loogle/grep/LeanSearch searches.
- `dag/nodes/sec-six-functors/lem-coef-finite-relative-lifting-recognition.json`: new statement-only lemma, status unsplit; Mathlib no match. It characterizes RLP for the finite relative tests, without asserting replacement existence, filtered-colimit preservation, mapping-test units, or perfectness.
- `citations.json`: one verbatim statement quotation for every node used by every step. Full statements are retained when a step uses several clauses of the same statement.

There is one new node and zero Mathlib leaves. The item's chapter and unit are unchanged. It is not a unit key statement, so no unit record is edited. All writes are in this item's sandbox; no Lean, compiler, Lake, or direct git operation was used.

## Attachments

None. Searches for the exact blueprint tag and for marked simplicial/Cartesian-fibration/saturation terminology in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no declaration of this item or the proposed new recognition lemma. The upstream master checkout was also searched for the exact item and the marked lifting notion; its sorry declarations are not treated as completed proofs.

## Wanted literature

WANTED: Jacob Lurie, Higher Topos Theory, Proposition 3.1.1.6 and Remark 3.1.1.10, Proposition 3.1.3.7 proof (1), printed pp.158-159, and Appendix A.2.6.7, A.2.6.12-14, for lem-coef-relative-cartesian-equivalence-saturation and lem-coef-finite-relative-lifting-recognition. The source is not archived in project literature. I read the online IAS PDF, in particular PDF pages 175-176 for the finite detector and replacement argument and PDF page 842 for perfectness. No source was downloaded or installed. The proof is therefore marked agent-written. No Stacks tag states this marked simplicial result, and no SGA source is used.

## Findings and corrections

The imported statement is accurate against HTT 3.1.3.7(1), including its important constant-base restriction on the detector and its explicit fiber-criterion hypothesis. It remains unchanged. Its proof was empty. I supplied the finite-cell construction rather than appealing to the relative model structure being constructed. The new lemma isolates the nontrivial finite-lifting recognition argument, which cannot be obtained by citing the existing statement about all marked-anodyne maps: the finite detector is not simply that entire generating family.

The perfectness proof expands the source's short appeal to A.2.6.14 with existing DAG statements. A disjoint coproduct of the vertex fibers gives a single filtered-colimit-preserving functor into the absolute marked category. Its inverse image of the absolute weak-equivalence class is exactly the relative class. Accessibility and closure under all filtered colimits are checked separately: accessibility alone would not supply the latter. No new generic perfectness lemma was created, since the existing accessible-arrow-inverse-image and model-weak-equivalences-accessible nodes suffice.

The only proof-route tools outside the unit are elementary filtered-colimit calculations on sets and the definitions of enhanced functors/cores. They are declared in split_report.tool_uses. This is below the blueprint's finite-coefficient mapping-complex adjunction through the recorded straightening ancestry; it replaces no step of the unit's geometric duality route. The unit text contains historical SGA references, but this split cites and uses none of them.

## Not duplicates

lem-coef-finite-relative-lifting-recognition vs lem-coef-relative-marked-anodyne-calculus: the existing node recognizes RLP against the full marked-anodyne class, including all countable Kan-marking generators; the new lemma replaces that infinite-domain family by the finite detector only at constant vertices. The existing statement does not give this reduction.

lem-coef-finite-relative-lifting-recognition vs lem-coef-marked-anodyne-lifting-calculus: the existing statement defines the detector and supplies its absolute mapping restriction, and recognizes full marked-anodyne RLP over a point; it does not recognize finite relative RLP over arbitrary S.

lem-coef-finite-relative-lifting-recognition vs lem-coef-infinity-marked-cocartesian-lifting: that node is opposite-variance, assumes both total space and base are quasicategories, and uses the entire marked-coanodyne class. It does not give the finite arbitrary-base assertion.

lem-coef-finite-relative-lifting-recognition vs lem-coef-relative-cartesian-equivalence-saturation: the item constructs and analyzes a finitary replacement and proves perfectness of its equivalences; the new lemma is only a horn/detector recognition criterion for a given marked map. The item's construction, mapping tests, fiber comparison, and small-generation proof stay in the eight steps.

lem-coef-finite-relative-lifting-recognition vs lem-coef-marked-saturation-perfect-equivalences: the existing node constructs an absolute replacement and characterizes its absolute equivalences, rather than stating the finite relative RLP criterion for a given map.

Before creating the new lemma I searched the whole DAG for the finite detector, first-three-generator lifting descriptions, 3.1.1.6 and 3.1.3.7, and used blueprint_refs.py search for relative cartesian equivalence saturation, cartesian fibration, finite relative lifting, marked, equivalence detector, and filtered colimits. No imported blueprint statement states the proposed recognition criterion; same_as is empty. I also read the accessible inverse-image statements found in those searches and reused them instead of creating a generic perfectness node.

## Review by NZ

I read the worker brief, the chapter and the actual unit sk-prop-sf-biduality-general, the three SETUP levels, GOAL and dag-sync, and sections B through E of delivery-errors in full. The blueprint ancestor is prop-coef-integral-exceptional-adjoint; I read its current main-20261015 proof, paragraph 2 containing the finite-coefficient derived mapping-complex adjunction. This item is supporting simplicial machinery through its recorded ancestry, not an assertion imported verbatim from that paragraph. I retained that distinction in blueprint.from and split_report.

For the item and the new lemma I checked HTT's finite detector construction and recognition argument in 3.1.3.7(1). In particular, all base maps are permitted for (i)-(iii), while the detector maps are only constant at vertices. The source's recognition does not assume the base or total space is a quasicategory. This is why the new statement has arbitrary simplicial S and X, and why it is a real lemma, not an elementary renaming of the full marked-anodyne criterion. The nontrivial argument to be split later is the horn proof that marked edges are Cartesian and supply all lifts, followed by comparison of an arbitrary Cartesian edge with a marked lift: their discrepancy in a vertex fiber is an equivalence, the detector marks it, and the marked composition condition marks the original edge. This explanation belongs here rather than inside the unsplit node's statement.

Step 1 uses the actual elementwise statement of lem-weil-pbc-filtered-colimit-sets-elementwise, which supplies both representatives and eventual equality, for finite maps and relations. It introduces the category and gives its colimits, finite generators, and finite presentability, so later accessibility applications have a verified locally presentable source. The finite relative recognition node explicitly defines precisely J_S; it is not cited for presentability. Finite means finitely many nondegenerate simplices, and the quotient detector is finite in that sense.

Step 2 carries the construction: every domain map indexes an attached cell, maps send each cell to its named image cell, and omega rounds suffice because every domain is finite. The cited recognition statement supplies the finite test family only. The filtered-colimit calculation uses the finite-Hom argument of Step 1, coproducts, pushouts, and interchange of colimits; it does not use a small-object theorem with the wrong preservation claim. This avoids treating a search hit about smallness along a cell chain as filtered-colimit preservation of the replacement functor.

Step 3 uses exactly the implication from finite RLP to naturally marked Cartesian in the new statement. Both its smallness and arbitrary-base hypotheses have been established. This is the only new non-elementary recognition input, and there is no appeal to the model structure in lem-coef-marked-relative-cartesian-model.

Step 4 uses three statements I opened: the relative calculus gives trivial Kan restriction for marked-anodyne maps and base change with the natural marking; the marked-anodyne lifting calculus gives the detector restriction isomorphism over a point; and Kan-Quillen supplies the boundary-RLP characterization of trivial Kan fibrations. Constant detector labels are essential to identify their relative mapping objects with absolute maps into Z_s. The product, pushout, and sequential-union assertions are justified by an explicit recursive boundary-lifting argument, so no unquoted preservation-of-weak-equivalence assertion is hidden in that passage.

Step 5 is the defining two-out-of-three calculation in the naturality square, using Kan weak equivalences and the units proved in Step 4. Its fiber criterion is exactly the hypothesis of this item, applied only to the natural Cartesian objects just constructed. The step is elementary relative to those facts; it is not a proof of the input criterion and does not invoke a relative model theorem.

Step 6 checks the absolute test class against functor inverses: test at C for surjectivity on components, then at D for injectivity. I read the relative calculus's statement that sharp maps are Kan cores over every base, and the enhanced-diagram definition of coherent natural equivalence and functor inverse. These clauses justify the homotopies actually used. The Kan model statement permits concatenating paths and recognizes homotopy equivalences as weak equivalences. The absolute saturation node supplies W_* and its tests, not an unstated fiber criterion.

Step 7 writes out both directions for the indexed coproduct. An inverse of the whole coproduct cannot cross labels, because its composite is naturally equivalent to the identity and an equivalence edge stays in a summand. This point matters for empty summands and is not replaced by the words 'equivalences are objectwise'. The finite-limit/filtered-colimit node explicitly includes fiber products and applies degreewise to a fiber over a fixed vertex, including its markings. Small S ensures a small coproduct, and the construction respects its index on every map.

Step 8 uses exactly the clauses I read in the four cited statements: the absolute point model is combinatorial; model weak equivalences form an accessible ambient arrow subcategory; inverse image under an accessible functor between locally presentable categories preserves accessibility; and the absolute marked-equivalence class is closed under all filtered colimits. Step 1 verifies local presentability and Step 7 verifies the functor preservation. The accessibility cardinal may change, as the inverse-image node warns; I claim no fixed omega bound for the small generator set. Every kappa-filtered diagram is filtered, which gives the required small generation under filtered colimits. The whole final perfectness claim remains in this step's argument, rather than being transferred into a new node.

For B1-B7, the new node is a self-contained statement with its objects, finite tests, RLP meaning, size conditions and base hypotheses written explicitly, real TeX, no proof or proof sketch in the statement, no proof dependencies, and the exact online source place. There is no spurious Stacks tag. It has blueprint ancestry and an empty same_as after the whole-blueprint search. The Mathlib searches were run with msearch.py; I read the Quasicategory/Basic.lean and SimplicialSet/CategoryWithFibrations.lean hits. They characterize unmarked quasicategories over a point or Kan fibrations, not the stated marked relative condition. The second phrasing still gives only those results. SSet finite presentability from the item's searches is an ingredient, not a match for the item. Searches for a generic perfect-class lemma were also logged while investigating the route, but no such new node is created or claimed.

I tested S empty, S a point, empty fibers, identity maps, and a base with noninvertible edges. Empty S leaves the terminal category of empty marked objects, so all conclusions and the empty coproduct test agree. Over a point the recognition and tests agree with the existing absolute nodes. A nerve of a category with a noninvertible arrow may carry that arrow marked as Cartesian over itself; the relative criterion allows it, whereas an erroneous requirement that all marked edges be total-space equivalences would fail this test. Constant detectors only force fiber equivalences to be marked, as required. Empty summands cannot be filled by inverse maps from a different index, and the coproduct proof handles them. The sequential construction need not fix already fibrant inputs, which the item does not demand. I found no statement dispute or hypothesis to add.

I checked C1/C4 citation by citation against the statements and supplied verbatim quotations. The existing perfectness/accessibility/absolute-model dependencies have no dependency path back to this item, so the proposed route does not create that cycle. I corrected my initial proposal to add a generic perfect-class inverse-image node: existing accessibility nodes already give what is needed, and keeping that elementary combination as a step avoids duplication. I also retained the explicit mapping-limit lifting proof instead of asserting that inverse limits preserve arbitrary weak equivalences.

## Unfinished work

No part of the item's one-level split remains unfinished. The new finite relative recognition lemma is deliberately statement-only for the next stage-1 worker. No delivery is authorized: this sandbox is left for the fresh second reader after the dry run.

## Dry-run repair

The first server preflight returned only a B2 wording check on Step 5: the phrase “the item’s statement” was not standalone wording. I replaced it by “the assumed fiber criterion” and made Step 8 refer directly to the defining clauses of perfectness. No mathematics, hypothesis, dependency, quotation, or new-node statement changed.

## Second reading by NZ

- Item statement: checked against Lurie, HTT Proposition 3.1.3.7(1), pp. 158–159 (PDF pp. 175–176), including the mapping-test definition of Cartesian equivalence, the finite detector, the fiber criterion input, the filtered-colimit replacement, and perfectness; all hypotheses and clauses agree.
- Step 1: checked against `lem-weil-pbc-filtered-colimit-sets-elementwise` and the finite-recognition node; finite simplex/marking data, empty objects, and arbitrary small base maps give the stated locally finitely presentable marked-over-base category.
- Step 2: checked against the finite-recognition statement and the explicit pushout construction; finite domains factor through a finite stage, the cell-indexing maps are functorial, and filtered colimits commute with the displayed finite data and pushouts.
- Step 3: checked against the finite-recognition statement; its RLP conclusion supplies the Cartesian fibration and exactly the natural Cartesian marking, with no quasicategory or relative-model hypothesis added.
- Step 4: checked against the relative marked-anodyne calculus, marked-anodyne lifting calculus, and Kan–Quillen statement; generator restrictions, constant-vertex detector restrictions, products/pullbacks, and the recursive boundary lifting for the countable tower give the asserted weak equivalence.
- Step 5: checked against the Kan weak-equivalence facts and the item’s explicitly assumed fiber criterion; naturality with the two units gives the two-out-of-three reduction to the naturally marked Cartesian targets.
- Step 6: checked against the absolute perfect-equivalence statement, enhanced-diagram definitions, relative mapping-core statement, and Kan weak-equivalence statement; the two mapping tests give both coherent inverse homotopies, including empty quasicategories.
- Step 7: checked against enhanced-diagram definitions, the relative marked-anodyne calculus, and filtered-colimits/finite-limits; indexed coproducts preserve and reflect equivalences labelwise, including empty index and empty summands, and the fiber functor preserves filtered colimits.
- Step 8: checked against the absolute marked-point model, accessible weak-equivalence, accessible inverse-image, and absolute perfectness statements; local presentability and filtered-colimit preservation are established in Steps 1 and 7, yielding accessibility and closure under all filtered colimits.
- New node `lem-coef-finite-relative-lifting-recognition`: checked against HTT Proposition 3.1.3.7(1), Proposition 3.1.1.6 and Remark 3.1.1.10; the arbitrary-base hypotheses, finite detector, constant-vertex restriction, exact natural marking, and absence of quasicategory assumptions agree. Its statement is self-contained through the two cited definition/calculus nodes, has no proof or proof dependencies, and its LeanFinder/LeanSearch/Loogle/grep searches were inspected with no exact match.

Changes made in this second reading:

- Added this source-based review, including the edge cases S empty, S a point, empty fibers/summands, identity maps, and a base with noninvertible edges; these cases agree with the statements and expose no missing hypothesis.
- No mathematical statement, proof step, dependency, citation quotation, or search record required correction. The delivery metadata for the new node already has `created.item` equal to this item; the item’s origin stamp is retained as maintainer metadata.
