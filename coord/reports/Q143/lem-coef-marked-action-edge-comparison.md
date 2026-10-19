## Files written

- dag/nodes/sec-six-functors/lem-coef-marked-action-edge-comparison.json: statement, split into four proof steps; no Mathlib match.
- citations.json: one verbatim statement quotation for each cited node in each numbered step.
- report.md: worker report and signed self-review.

No new nodes; zero new Mathlib leaves. searches.jsonl records the searches actually run by msearch.py.

## Attachments

None. I searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the exact item id, marked/action expressions, SSet, quasicategory and QCat, and checked the exact upstream master reference. No project declaration states the item. Upstream master is reference material only. The item has no recorded Lean audit or declaration to attach.

## Wanted literature

WANTED: Lurie, Higher Topos Theory, Proposition 3.2.1.11(4), printed p.176, final paragraph, for lem-coef-marked-action-edge-comparison. Read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; no HTT archive was found under literature/. The interval formula and proof details are therefore recorded with proof_origin.by = agent.

WANTED: Kerodon, Subsection 4.6.8 (01PF), Remarks 4.6.8.10 and 4.6.8.14, for the existing lem-coef-infinity-mapping-composition used by this item. Read online at https://kerodon.net/tag/01PF. These are Kerodon references, not Stacks tags; no Stacks tag states this marked simplicial comparison.

## Findings and corrections

The imported item had an empty proof. Its statement is correct and is unchanged, including the iff direction, unmarked e, arbitrary parameter simplicial set, and absence of Kan hypotheses on A, U or V. I supplied a degreewise minimum homotopy and a triangle with its three faces specified; cancellation by its marked side proves both directions. This avoids assuming a general theorem that an unspecified simplicial homotopy preserves equivalences. No statement dispute or target change is needed.

I read the chapter and sk-prop-sf-biduality-general unit records. This is a technical child below paragraph 2 of prop-coef-integral-exceptional-adjoint through the recorded marked-cone generator ancestry, not the key node of the unit. Unit realization fields do not change. All non-definition proof citations are in the item's unit; no off-route tool use is needed. No SGA source is used.

## Existing-node and Mathlib searches

Whole-DAG statement searches for homotopy categories, triangles and equivalences found lem-coef-infinity-mapping-composition, which already states exactly the triangle relation and the inverse-triangle equivalence criterion needed. I read its full statement and metadata. A dependency traversal found no path from it back to the item. The outer-horn and localization-homotopy-category nodes were also inspected but are unnecessary. The whole-blueprint searches with tools/blueprint_refs.py for equivalence edges, marked action and mapping composition returned no blueprint duplicate. The ancestor command confirms prop-coef-integral-exceptional-adjoint. The inherited from.place was already specific and is retained; same_as remains [].

msearch.py ran LeanFinder with the marked-action statement and a second formulation in terms of a simplicial square and invertible edges, LeanSearch with triangle cancellation, Loogle with "SSet", "Marked", and a whole-Mathlib grep for marked actions. All returned normally. I read the actual LeanFinder log left by the interrupted tool session before continuing; there was no delivery in progress to repeat. Searches are appended to the item's existing records without deleting the original Q103 searches.

The candidates read were NerveAdjunction.lean (strict Segal lift edge formulas), CompStruct.lean (edge map and identity formulas), StrictSegal.lean (spine edge formulas), ProdStdSimplex.lean:50-80 (product face formulas), Quasicategory/TwoTruncated.lean:35-105,245-285 (horn fillers and equality/composition in the truncated homotopy category), and Quasicategory/Basic.lean (inner-horn filling definitions). They provide useful unmarked ingredients but none states this arbitrary marked-action comparison or covers all of it by a one-line specialization. The three grep hits were unrelated comments in NonUnitalHom.lean, StackTuringMachine.lean, and Scheme.lean; I opened their reported lines. No Mathlib leaf is claimed.

## Unfinished work

None for this one-level split. Existing dependencies retain their own stage-1 status. No Lean file, compiler, Lake, build, live project file or launcher file was written or run.

## Not duplicates

No new nodes were created. The short monotone-map construction, marking argument and ordinary-category cancellation remain proof steps, rather than elementary nodes or restatements of clauses of the item.

## Review by Q143

I read the HTT final paragraph on printed p.176 online, where the parameter edge is compared with an endpoint edge through a homotopy whose side edges are marked. I also read Kerodon 01PF, in particular the component-composition construction and ordinary homotopy-category description, and opened the full statements of all three cited DAG nodes. The statement keeps precisely the hypotheses needed by that argument. I checked delivery-errors B through E against the actual node, sources and citations; the corrections below are mathematical details, not just mechanical checks.

Step 1 uses def-cbc-enhanced-diagrams-cones for standard simplices as monotone maps with precomposition and for degreewise products. Minimum is order preserving, and minimum commutes with evaluation after every operator. The formula H(r,t) therefore gives a simplicial map, with endpoints H(0,t) = mu(a_0,e(t)) and H(1,t) = mu(g(t),e(t)). These equalities are direct checks of the two possible interval values. No horn-filling property is needed for the parameter, source or target of mu. This construction is elementary; it is not a new lemma hidden inside the step.

Step 2 uses exactly the statement of lem-coef-marked-point-cartesian-model defining marked maps, degenerate marked edges and coordinatewise product markings. Since all edges of A sharp are marked and the edge at y_1 is degenerate in Y, their pair is marked even when e is not. The stated hypothesis on h then makes its image an equivalence. We use only the marking clauses of that large node, not its model-structure proof. This step is elementary.

Step 3 uses def-cbc-enhanced-diagrams-cones to construct j from alpha = (0,0,1) and beta = (0,1,1), and lem-coef-infinity-mapping-composition for both the 2-simplex relation and the equivalence/invertibility characterization. Those assertions are present verbatim in the latter's statement, not merely in its proof. Restriction to 01 fixes r = 0 and moves t; restriction to 12 fixes t = 1 and moves r; restriction to 02 moves both. The three edges are consequently the initial vertex action, the marked side v, and the diagonal action, with matching vertices. All mapping-composition hypotheses hold because Z, rather than A, U or V, is a small quasicategory. In hZ the long class is v times the first class. I checked both inverse calculations, including the reverse implication by multiplying on the left by v inverse. The non-elementary composition theorem is cited, and the remaining cancellation is elementary algebra in the supplied ordinary category. We do not claim that the definition of equivalence alone supplies composition or cancellation.

Step 4 uses the already proved iff at the vertex g(0); its universal-quantifier deduction is elementary. It adds no unsupported lemma.

Small cases checked: a degenerate g gives the same edge on both sides and a degenerate marked side; a degenerate e makes the source pair (g,e) marked, so the conclusion agrees with the marked-map hypothesis; A = Delta^0 is the identity comparison. If A is empty there are no edges; if U is empty there is no e. Ordinary category nerves give the same equation with an invertible side, including a bottom edge which is not invertible. Thus the proof does not silently assume the bottom edge or all edges of the parameter are equivalences before applying mu. In particular, A = Delta^1 is allowed despite its noninvertible edge. All steps are below 2000 characters; no long step hides an independent comparison lemma.

I corrected only the missing proof and its dependencies and search/report fields. The four citation entries use exact substrings of the opened statements, verified while writing citations.json. proof_deps is the union of uses. No new unsplit statement, new definition, duplicate, hypothesis change or source-route replacement remains to review. The maintainer still supplies the independent delivery review required by the direct-delivery brief.
