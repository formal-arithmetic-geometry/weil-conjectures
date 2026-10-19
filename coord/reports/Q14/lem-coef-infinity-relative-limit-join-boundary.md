# Worker report: lem-coef-infinity-relative-limit-join-boundary

1. Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-relative-limit-join-boundary.json`: statement split into three proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-relative-slice-inner-fibration.json`: new statement-only prerequisite; no Mathlib match.
- `citations.json`: 13 verbatim step/node citations.

2. Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item id, relative-limit join terminology, and likely declaration names. No project declaration states this item without `sorry`.

3. WANTED:

WANTED: Lurie, *Higher Topos Theory*, Definition 4.3.1.1, Remark 4.3.1.2, Proposition 2.1.2.1, and the opposite limit form, for the relative fixed-diagram join-slice criterion.

WANTED: Kerodon online sources 018F, 018J and 02WS (the shared literature archive has no archived infinity-categorical source for these statements).

4. Corrections and route

The imported item statement is well typed and was retained. Its proof field was empty, so I supplied the fixed-diagram route used by its citer. The new helper isolates the nontrivial induced-map assertion: an inner fibration induces an inner fibration on sharp join slices with a fixed diagram. It is strictly smaller than the item and has no proof hidden in its statement. The item proof then (i) constructs the two slices and their induced map, (ii) translates the relative-limit homotopy-pullback square into the fixed-boundary mapping-space comparison, and (iii) applies the dual relative-final boundary criterion. The $K=\varnothing$ case is explicitly included. No SGA source is used.

## Not duplicates

- `lem-coef-infinity-relative-slice-inner-fibration` vs `lem-coef-infinity-slice-right-fibration`: the existing node proves that one fixed slice projects by a right fibration; the new node proves that postcomposition by an arbitrary inner fibration gives an inner fibration between two fixed slices.
- `lem-coef-infinity-relative-slice-inner-fibration` vs `lem-coef-infinity-join-cocone-associativity`: the existing node gives the quasicategory and isofibration of a single sharp cocone slice and its associativity; it does not state inner-horn lifting for a map induced by $q:E\to D$.
- `lem-coef-infinity-relative-limit-join-boundary` vs `lem-coef-infinity-relative-cone-initial-corner`: the existing node characterizes relative limits as final vertices in an internal functor-category cone construction; this item uses the fixed-diagram sharp join slice and the boundary-filling equivalence, whose simplices retain the fixed $K$-diagram.
- `lem-coef-infinity-relative-limit-join-boundary` vs `lem-coef-infinity-relative-initial-boundary`: the existing node is the general relative-initial/relative-final boundary criterion; this item supplies the special fixed join-slice final object arising from a relative limit and translates its boundary data to $\partial\Delta^d\star K$.

- `lem-coef-infinity-relative-slice-inner-fibration` vs `lem-coef-infinity-anodyne-cocones`: 018J gives the pushout-join inclusion as inner anodyne, while the new node applies that inclusion to prove the induced map between two fixed join slices has inner-horn lifting.
- `lem-coef-infinity-relative-slice-inner-fibration` vs `def-coef-infinity-right-anodyne`: 018J in the existing definition only defines right-anodyne closure and does not state any induced slice map or inner-fibration conclusion.
- `lem-coef-infinity-relative-slice-inner-fibration` vs `lem-coef-infinity-pushout-join-saturation`: 018J in the existing saturation lemma concerns closure of a pushout-join class under saturation; it does not assert postcomposition by an inner fibration on fixed join slices.
- `lem-coef-infinity-relative-slice-inner-fibration` vs `lem-coef-infinity-terminal-anodyne`: 018J in the existing terminal-anodyne lemma concerns a terminal join inclusion; it does not state the fixed-diagram slice construction or the induced inner-fibration property.

## Review by Q14

I read the item JSON, the `sec-six-functors` chapter record, and unit `sk-prop-sf-biduality-general`. I also read the complete statements of `def-cbc-enhanced-diagrams-cones`, `def-coef-infinity-fibrations`, `def-coef-infinity-relative-cone`, `lem-coef-infinity-slice-right-fibration`, `lem-coef-infinity-join-cocone-associativity`, `lem-cbc-enhanced-functor-cone-calculus`, `lem-coef-infinity-relative-initial-boundary`, and the new helper. The source search found no existing Lean declaration or blueprint node for the item or helper.

Step 1 uses the slice-right-fibration statement for the exact degreewise model $\Delta^n\star K\to E$, the helper for the induced inner fibration, and join-cocone associativity for currying maps into the slice. I checked that the boundary factor is the final $K$ block, matching the item's $\partial\Delta^d\star K$ order, and that the postcomposition map has base $D_{/qf}$. The cited fibration definition supplies the inner-horn convention.

Step 2 uses the relative-cone definition's homotopy-pullback square with the limit orientation, together with the coherent mapping-space and join-associativity statements. Taking the homotopy fiber over the fixed boundary $f$ and $qf$ gives exactly the maps between fixed join-slice mapping spaces. I checked that this is a fiber comparison, not an identification of the internal cone category with the fixed slice. The source is HTT Definition 4.3.1.1 and Remark 4.3.1.2 in the dual form.

Step 3 uses the dual clause of the relative-initial-boundary theorem. Its final-vertex convention matches $\{d\}\star K=c$, and its explicit exclusion of dimension-zero fillers matches the item's $d>0$. I checked the currying and uncurrying on every face and the empty-$K$ case. The resulting filler has both exact equations required by the item.

I tested edge cases on paper: $K=\varnothing$, $d=1$, $q=\mathrm{id}$, and $E\to D$ the terminal map. The statements reduce respectively to the final-object boundary criterion, the universal comparison edge, ordinary join-slice lifting, and the absolute limit case. All citations in `citations.json` are verbatim substrings of the cited node statements. No Lean file, compiler, Lake build, or live project file was touched.

5. Remaining work

The helper is intentionally statement-only and enters the stage-1 queue. The item is ready for the second reader and required dry run.


## Second reading by Q14

This reading supersedes the first reader's helper/three-step description; the earlier sections, including "## Review by Q14", are retained as requested. The delivered item has five steps, zero new nodes and zero new Mathlib leaves. Its statement is byte-for-byte unchanged from the shared item.

- Original step 1: checked each cited statement, Kerodon 018F/018J and HTT Proposition 2.1.2.1; repair required: the helper is a few-line consequence and the cited cocone associator has the opposite join orientation.
- Original step 2: checked the complete relative-cone definition, join-cocone associativity and coherent cone calculus, against Kerodon 02X1/02XB/04J5; repair required: associativity does not identify sharp-slice mapping spaces with homotopy fibers of internal cone mapping spaces, and that comparison was not cited.
- Original step 3: checked the complete relative-initial-boundary statement against Kerodon 02WS; the final-vertex and positive-dimension convention is correct, but the claimed "unique prescribed-boundary lifting problem" proves no existence. Replaced it by the cited existence criterion and explicit currying formulas.
- New node `lem-coef-infinity-relative-slice-inner-fibration`: checked every hypothesis against Kerodon 018J and HTT Proposition 2.1.2.1; true, including empty K, but unnecessary. Removed: first lift the apex inner horn against q, then apply the existing pushout-join lemma with the empty-to-K monomorphism and lift the resulting inner-anodyne inclusion. These are the two lifts in final step 1. No statement-only node remains needing B1-B7 repairs.
- Final step 1: checked the exact degreewise model and quasicategory clause in `lem-coef-infinity-slice-right-fibration`, the right-anodyne-horn/monomorphism clause in `lem-coef-infinity-anodyne-cocones`, and the lifting definition in `def-coef-infinity-fibrations`, against 018F/018J; PASS. The preliminary apex lift is essential: the pushout-join lemma requires the entire apex simplex, not just its horn.
- Final step 2: checked the natural equivalence in `lem-coef-join-slice-cocone-comparison`, the order reversal and mapping-space duality in `lem-coef-infinity-relative-cone-equivalence`(4), and the full statement of `lem-cbc-enhanced-functor-cone-calculus`, against the comparison diagram in Kerodon 02XB and Example 04J5; PASS. Taking opposites converts cocones to cones. The proof gives the actual fiber formula and explains why precomposition with the comparison commutes with q; it asserts an equivalence, not an isomorphism between internal and sharp cone simplicial sets.
- Final step 3: checked the exact dual clause of `lem-coef-infinity-relative-cone-constant-test`, and the complete path-pullback invariance/pasting statements, against Kerodon 02X1 (constant-source condition); PASS. It writes A, B, C, H and the fiber at the actual coherent cone lambda, then gives both homotopy-pullback operations producing the base fiber at q-lambda.
- Final step 4: checked the dual clause of `lem-coef-infinity-relative-initial-boundary` against Kerodon 02WS, conditions (1)/(3); PASS. The functor is an inner fibration by step 1 and the vertex is relatively final by step 3. No isofibration assumption is inserted.
- Final step 5: checked the degreewise join formula of `def-coef-infinity-relative-cone` and the slice operators of `lem-coef-infinity-slice-right-fibration`; PASS. The simplex formula is compatible with every operator, retains the entire fixed K-diagram, and proves both required equations after gluing. No further associativity theorem is needed.

Changes and reasons:

- Removed the sole new helper and its citations: it is elementary from an already cited join lemma, rather than another stage-1 task.
- Replaced the unsupported sharp/internal mapping-space identification by the existing sharp/coherent comparison, its explicit opposite construction, the cone mapping-space formula and the existing constant-cone test.
- Wrote the homotopy-fiber/pasting calculation rather than saying that a homotopy-pullback square "transports" finality.
- Separated the final-object criterion from simplexwise currying/uncurrying; deleted the misleading uniqueness phrase and expanded the empty-K check.
- Replaced the source metadata with the Kerodon labels actually read online: Definition 7.1.6.1 (02KG), Propositions 7.1.6.19 (02X1), 7.1.6.13 (02XB), 4.3.6.4 (018J), Example 4.6.6.8 (04J5), and Corollary 7.1.5.17 (02WS). Read HTT Definition 4.3.1.1/Remark 4.3.1.2 and Proposition 2.1.2.1 directly online as a cross-check. The old metadata's Higher Algebra application is unnecessary and was not retained as an independently verified reference. There is no Stacks .tex tag for these infinity-categorical facts, and no SGA source is used.
- Regenerated `citations.json`: 12 citations, one verbatim extract from the cited node statement for every use in the five steps. Each quote was mechanically checked as a substring of the actual cited statement.

Small-case tests: for K empty the slices are E and D, the cone maps are identities on the apices, and the conclusion is exactly relative-final boundary lifting. For d=1 the boundary consists of the two apex vertices together with their fixed cones, and the filler is the comparison edge over the prescribed base edge; d=0 is correctly excluded (an arbitrary final object need not lift arbitrary unrelated base vertices). For q the identity, each proposed filler is already the prescribed base diagram. For E to a point, the square becomes the ordinary limit-cone universal property and its sharp-slice final-object criterion. If E is empty there is no c, so the assertion is vacuous. These checks reveal no missing hypotheses or statement dispute.

Duplicate/search audit: searched the shared DAG by 018J, 04J5, 02X1, 02KG and by slice/comparison/relative-limit vocabulary, and searched the current main-20261015 blueprint and the named upstream/slopmaster2 Lean directories by item id and mathematical keywords. The item is not already a closed Lean theorem; the lone unrelated Lean relative-limit-presentation hit concerns pro-objects. The existing sharp-to-coherent comparison and constant-test nodes supply the needed work, so no new blueprint duplicate is created. Independently ran msearch with leanfinder queries "Simplicial set slice comparison of sharp joins with functor category fibers" and "Simplicial set join with a fixed diagram preserves the inner horn lifting property", and grep "InnerFibration|innerFibration|rightAnodyne|RightAnodyne". The actual hits are in searches.jsonl; they give general simplicial-set foundations, horn filling, inner fibration definitions and cartesian pushout products, not a declaration of the item's fixed sharp-slice boundary theorem. Read Mathlib/AlgebraicTopology/Quasicategory/InnerFibration.lean directly to confirm the distinction. No new Mathlib leaf.

Route: all newly used infinity-category comparison/constant-test/pasting nodes have the item's unit, sk-prop-sf-biduality-general. `lem-cbc-enhanced-functor-cone-calculus` has unit sk-prop-sf-cbc and is used solely as the general tool for equivalences on mapping spaces and the coherent cone mapping-space formula; no node of the item's unit states that general comma formula. This is the same generic tool already used by the original split. Any needed tool-use authorization is for the maintainer to record; no tool_uses or unit metadata was edited. Inspected the current blueprint ancestor's proof paragraph 2; the five steps provide the same rectification/operadic prerequisite serving its derived coefficient adjunction, with no route change.

Only the sandbox item, citations, report and search log were changed. No live project or launcher was written, no git command was run in the shared tree, and no Lean/compiler/Lake/build or local preflight/check_dag/review_split command was run. The required server dry run and delivery follow this completed report.
