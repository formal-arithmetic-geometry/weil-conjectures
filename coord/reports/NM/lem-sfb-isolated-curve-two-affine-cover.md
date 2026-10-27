# Worker report: lem-sfb-isolated-curve-two-affine-cover

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-isolated-curve-two-affine-cover.json: statement, split; no exact Mathlib match.
- citations.json: verbatim statements for every node used by every numbered proof step.
- report.md: this report.

No new nodes; no new Mathlib leaves. The local write_split.py is a sandbox preparation helper, not a project file.

## Attachments

None. I searched lean/WeilConjectures for the blueprint tag, isolated curves, two-affine covers, finite-point affine neighbourhoods and the curve geometry. The existing affine-core and projective-space neighbourhood declarations do not state all clauses under the item's hypotheses. There is no attachment claim. All inherited Mathlib searches were retained; I also ran the prescribed msearch command with LeanSearch, two LeanFinder phrasings, Loogle and a Mathlib grep. The results concern arbitrary affine covers, Proj charts, affine-open properties and elliptic-curve code, not the required cover. The log is searches.jsonl. No compiler or Lean/Lake tool was run.

## WANTED

None.

## Errors or limitations in the input

No mathematical statement dispute and no statement change. The original node supplied only the statement. The source really gives the two-open construction: Stacks 0DZP first chooses U_2 containing the marked points and all component generic points, then chooses U_1 in the complement of the marked points. I made its suppressed finite-complement argument and the finite-type conclusions explicit.

The inherited blueprint.from.node is null. Running tools/blueprint_refs.py ancestor on the item reports None; its upstream created.item chain is already broken. Its detailed inherited from.place and via list are preserved, and split_report.blueprint explains the local source place realized. No ancestor was invented or another worker's node edited. Whole-blueprint searches for affine neighbourhoods, two affine opens, finite complements, finite sets and curve covers found no duplicate of the item. The existing ampleness and finite-point-neighbourhood nodes were reused.

There is a notation collision in the ambient DAG: def-weil-closed-points reserves |X| for closed points, whereas the item uses |X| in the conventional underlying-space sense and immediately requires P to consist of closed points. Either reading imposes the same finite-closed-point hypothesis here; I preserved the statement.

## Unfinished work

None in this one-level split. Four geometric facts are reused as generic tools from other units, declared in split_report.tool_uses: lem-sc-dim-one-ample-invertible, lem-sc-ample-finite-set-affine, lem-sc-ample-finite-principal-affine and lem-sc-dim0-finite. These implement the actual Stacks 0DZP affine-neighbourhood route inside the formal-lifting input; they do not replace the unit's alteration argument. All other proof inputs are definitions or existing Mathlib leaves.

## Not duplicates

No new nodes, hence no new/existing pairs. In particular I did not recreate 0A25/09NZ ampleness, 01ZY affine neighbourhoods, 09NV prescribed-open affine neighbourhoods, or 01KP affine intersections. Their existing node statements were opened and used directly.

## Review by NM

I read the chapter and unit records, the stage-1 rules, SETUP's three-level rule, GOAL.md and delivery-errors B through E. For the item's mathematics I read examples-defos.tex, Tag 0DZP (lemma-curve-isolated), its complete first proof paragraph, together with varieties.tex Tag 0A25 and properties.tex Tags 01ZY and 09NV. I read schemes.tex Tag 01KP and morphisms.tex's composition-of-finite-type passage for the additional asserted properties. There are no new nodes whose source must be checked. I opened every cited node statement, and citations.json reproduces the statements actually used.

Step 1 uses the definition of a Noetherian ring, the affine spectrum and locally Noetherian schemes, then the finite-type-over-Noetherian theorem. The field's two ideals supply its Noetherianity directly, so the theorem's base hypothesis holds. It gives precisely the Noetherian scheme needed in step 2; finite type is the given structure morphism.

Step 2 uses finite components for a Noetherian scheme, scheme sobriety to obtain their generic points, the ample-sheaf existence theorem with exactly separatedness, finite type and dimension at most one, and the finite-set affine-neighbourhood theorem applied to the union with P. Neither reducedness, smoothness, connectedness nor algebraic closure of k is added. The ample-sheaf theorem's statement includes the empty case. These cited statements supply the whole data taken from them, rather than relying on their proofs.

Step 3 cites the definition of dimension, the general irreducible-component containment theorem and the finite-type dimension-zero closed-subset theorem. For a hypothetical strict chain A inside B in the closed complement F, B sits inside a component C. Its generic point lies in V, so B is strictly inside C, giving a forbidden length-two chain in X. This proves dim F at most zero, including empty F, before applying lem-sc-dim0-finite. That cited theorem assumes only finite type over a field and closedness of F, both present. No irreducibility of X is assumed.

Step 4 uses the 09NV node, whose actual statement gives an affine neighbourhood inside a prescribed open, unlike the weaker 01ZY node. I checked E=F is finite and lies in W=X minus P, that W is open because P is a finite set of closed points, and that the ample sheaf is still on X. Thus the step does not silently require ampleness to restrict to a non-quasi-compact open. The cover equality and avoidance follow immediately from the displayed inclusions.

Step 5 uses the existing separated-over-affine-base intersection theorem, under the original separated structure map to Spec k. Its statement explicitly makes U intersect V affine. Quasi-separatedness alone is never used to claim affine intersections.

Step 6 uses affine-scheme quasi-compactness, separated-implies-quasi-separated, the triangle quasi-compactness lemma, quasi-compact-open-immersion finite type, and finite-type composition. I checked the triangle's base is Spec k, the source T is affine and hence quasi-compact, and X to Spec k is quasi-separated. Thus the middle open immersion is genuinely quasi-compact before invoking its finite-type lemma. The composition lemma supplies finite type over k for all three T, not just local finite type. No unproved general assertion that all open immersions are of finite type is used.

Step 7 applies exactly the open-immersion/smooth-composition statement to U and U intersect V inside W, whose smoothness is the hypothesis. It does not assert V is smooth. The required map factorization is the canonical restriction between open subschemes, not a general morphism factorization inferred from an image inclusion.

I tested X empty, P empty, dimension-zero schemes with P=X, disconnected curves, nonreduced curves supported at marked singularities, and a singular projective curve with smooth complement. Empty affine opens are permitted and both neighbourhood inputs allow empty finite sets. For P=X in dimension zero the second open is empty; the first contains all points. Over finite fields no hyperplane-avoidance assumption or infinite-field argument is made. All proof steps are shorter than 2000 characters. I checked B's self-containment and search honesty, C1/C4's statement coverage, D's prohibition on relabelling/cycles, and E's hypotheses and edge cases against the actual node statements. The split introduces no new lemma, no weaker item, and no source outside the permitted route.

## Repair of the returned delivery

The return at 2026-10-22 07:10 UTC identifies the reviewed branch head as dd9a1a37fcd and says the side completion was not promoted into the live queue DAG. I retained that delivery's sandbox proof, sources, search records and report. The current read clone has this item as unsplit, with the same statement, statement dependencies, source and blueprint ancestry as the retained copy. The delivery tool's first resumed dry run rebased the retained work onto current origin/sheaf-dag and exited successfully, producing 17a4ef09dfa without pushing.

I re-read all 19 distinct cited node statements in the current DAG, including the four off-unit geometric tools, rather than assuming that the prior approval still applied. Every retained citation quote is still verbatim in its current statement. In particular, the ample-sheaf input still includes dimension at most one and the empty case; the second affine-neighbourhood input still places its affine open inside a prescribed open; the finite-complement theorem still applies to any closed dimension-zero subset of a finite-type scheme; and the quasi-compact triangle input still assumes only quasi-separatedness of the middle scheme over the base. These hypotheses are supplied in steps 2, 4, 3 and 6 respectively. No current cited statement requires a change of the proof route or of the item.

I adjusted step 3 to cite lem-sc-scheme-sober explicitly for the generic point in the component, and spelled out the witness showing that the component cannot equal the closed subset B. This makes its dependency on the actual generic-point statement visible in that step as well as in step 2. I regenerated citations.json from the current cited statements, including this additional step/node pair. The proof still works for the empty scheme, a zero-dimensional scheme, an empty marked set and arbitrary base fields. There are no new nodes, changed hypotheses or long proof steps. This report and the adjusted split record the repair; the final delivery is built on the current live base by the prescribed tool.


## Current repair audit of the retained delivery

The resumed dry run exited 0 with `OK (not pushed)` at 51c4ac6de48. It built the retained delivery on the current server base; no manual git operation was used. I then compared the sandbox item with the current read-clone item: the live status is unsplit, and only the proof, proof dependencies, proof origin, Mathlib searches, split report and status differ. The statement, statement dependencies, source, chapter, unit and inherited blueprint fields agree. The earlier report and search records above remain retained history, not claims that this pass reran the searches.

I opened all 19 distinct proof-dependency statements again, plus all six statement dependencies. Each of the 20 citation step/node pairs in citations.json is still a verbatim part of the current cited statement, and these pairs cover every uses entry exactly. Thus none of the current cited statements changes the retained mathematical route. In particular step 3 uses the generic-point statement itself to witness that B is strictly smaller than C; step 4 uses the stronger prescribed-open version 09NV rather than 01ZY alone; step 6 uses quasi-separatedness of X over Spec k to apply the triangle lemma. The four generic tool uses remain declared for maintainer review.

For the source audit I reopened examples-defos.tex lines 2814–2852 (0DZP), properties.tex lines 5244–5255 (01ZY) and 5293–5301 (09NV), and varieties.tex lines 9202–9214 (0A25). The source's affine choices agree with the retained proof. I adjusted step 4 to give the choice U empty explicitly when F is empty, using Spec of the zero ring. This also checks the case V=X directly; X empty and dimension-zero X with P=X cause no extra nonempty-neighbourhood assumption. For nonempty F the existing 09NV application has exactly its stated finite-set and prescribed-open hypotheses. This is the only new mathematical clarification in this resumed repair; the statement and dependency sets are unchanged.

I repeated the project-source search for the exact blueprint tag and the two-affine-cover and isolated-curve notions. There is no exact project declaration to attach. The whole-blueprint search for “two affine” finds only the unrelated linear-pair gluing node. The ancestor command still returns None, so the existing recorded ancestry limitation is unchanged. No new node or Mathlib leaf was introduced; all retained searches and their results remain available. Every proof step remains below 2000 characters. The final dry run and push follow this renewed audit.


## Repair of returned head 5c7edff7a65

The current return entry is dated 2026-10-22 13:36 UTC and again reports that the approved side completion was not promoted into the live queue DAG. The retained sandbox already contains the earlier reviewed proof and its subsequent clarifications. I checked the current return and ledger before repeating delivery: there is no recorded merge of this item and no surviving delivery process. The required initial resumed dry run exited successfully at 7e1dc96f933, built on the current server base by deliver.py.

The current read-clone item remains unsplit. Comparing its fields with the retained sandbox gives differences only in proof, proof dependencies, proof origin, Mathlib searches, split report and status. In particular the statement, its six statement dependencies and its blueprint ancestry remain unchanged. I reopened all 19 distinct cited statements and all six statement dependencies. Every one of the 20 step/node citation pairs still matches its verbatim quote, with exact coverage of the proof's uses lists. No citation needs replacing: the finite-type Noetherian input in step 1, generic points and ampleness in step 2, dimension-zero finiteness in step 3, prescribed-open neighbourhood in step 4, separated affine intersection in step 5, quasi-compact triangle in step 6 and smooth open restriction in step 7 still say precisely what those steps use.

I reopened Stacks 0DZP (lemma-curve-isolated) and the affine choices in its first proof paragraph, together with 0A25, 01ZY and 09NV. The route and hypotheses continue to agree with those sources. I adjusted step 4 so that the empty-complement case is handled first, explicitly using the spectrum of the zero ring and its lack of prime ideals; only the nonempty case invokes the prescribed-open affine-neighbourhood theorem. Thus the proof itself now spells out the affine choice for V=X, including X empty or zero-dimensional X with P=X, before making the other choice. P empty and arbitrary base fields remain permitted. This clarification and the renewed audit are retained in this repair, rather than sending an unchanged rebase.

The renewed narrow source search finds no declaration stating the whole item; the blueprint search again finds no duplicate. I read and reused searches.jsonl and the retained Mathlib results without claiming any new search invocation. No new node or Mathlib leaf is needed, no step exceeds 2000 characters, and no Lean source or compiler was used. The delivery command will create the repaired commit on the then-current live base; the server-side promotion failure itself is a maintainer operation outside this worker's sandbox authority.


## Repair of returned head e5a321d1260 (2026-10-23)

The return dated 2026-10-22 16:30 UTC again concerns promotion of the approved side completion into the live queue DAG. I retained the delivered proof, report, sources and Mathlib searches. The required initial dry run completed with `OK (not pushed)` at 0de1db03e72 on the current server base. The current read-clone item is still unsplit; comparison with the retained item found only the worker-owned proof, dependency, search, split-report and status fields different. Its statement, statement dependencies, source and inherited blueprint ancestry agree. The previous returned heads and their repairs remain documented above.

I re-read all 19 existing proof inputs and all six statement inputs from the current DAG. All 20 retained step/node quotes remain verbatim, including the finite-type dimension-zero closed-subset lemma, the prescribed-open affine-neighbourhood lemma and the quasi-compactness-in-a-triangle lemma. No current citation requires replacing the retained route. I reopened Stacks 0DZP's complete first paragraph, 0A25's ampleness argument, and the statements of 01ZY and 09NV; their hypotheses are still exactly those supplied in steps 1–4. The project-source search found no exact declaration to attach: the affine-core theorem requires a smooth geometrically connected curve and supplies neither the marked-point neighbourhood nor the whole conclusion. The whole-blueprint search and ancestor check retain the previously reported results. I read searches.jsonl and all recorded result lists; these searches are reused, not represented as fresh invocations.

This pass repairs a concrete citation omission in step 4: its explicit construction of the empty affine open now cites def-weil-affine-spectrum for the prime-ideal description and def-pc-scheme for the definition of affineness. The zero ring has no proper prime ideals, giving the empty spectrum directly; this uses no extra geometric lemma. I added both step/node pairs to citations.json and included def-pc-scheme in proof_deps. The resulting 22 quotes cover every uses entry exactly. The empty scheme, the case V=X, dimension-zero X with P=X, P empty and nonreduced or disconnected curves all remain allowed. In particular the correction neither assumes a point exists nor introduces smoothness of V.

For the B–E audit there are still no new nodes or Mathlib leaves, no statement change, no hidden long step, and no changed unit route. Every proof step remains shorter than 2000 characters. The four geometric tools remain declared for maintainer review. I rewrote split_report.summary around the final mathematical split and this actual repair, leaving the retained repair history in this report. Only sandbox files were written; no Lean, compiler, build, manual git operation, launcher edit or repository edit was used. The remaining live-DAG promotion itself is the maintainer's operation; this delivery supplies the repaired split on the current base for that operation.
