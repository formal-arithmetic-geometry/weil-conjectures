# Q19 stage-1 repair: lem-cbc-mapping-simplex-universal-equivalence

## Files written

- dag/nodes/sec-smooth-purity/lem-cbc-mapping-simplex-universal-equivalence.json: seven-step split; revalidated current citations, reused the current final-edge node, and retained the exact current item statement. No Mathlib match.
- dag/nodes/sec-smooth-purity/lem-cbc-simplexwise-categorical-base-change.json: the one remaining new statement-only node, HTT Proposition 3.2.2.8; unsplit, no Mathlib match. Its previously searched statement is unchanged.
- citations.json: all 14 step/node pairs, each quoting an actual part of the currently cited statement. The two construction quotations and the final-edge citation were repaired.
- repair-review.json: hashes of the statements read during this repair, including the existing final-edge node. This is sandbox evidence only.

The unlanded file lem-cbc-mapping-simplex-last-edge-composition.json was removed because the current DAG already contains the same theorem as lem-coef-mapping-simplex-final-edge. It is not delivered. searches.jsonl and prepare_split.py are retained scratch from the earlier work; prepare_split.py was not rerun. There is one new node and zero Mathlib leaves.

## Attachments

None. This repair repeated exact-id and mapping-simplex/quasi-equivalence searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures, and exact-child-id/concept searches in the reference master checkout and dag/lean_names_upstream.json. No matching project declaration was found. The master checkout is reference material only. No Lean was written and no compiler, Lake or build tool was run.

## WANTED

WANTED: archival copy of Jacob Lurie, Higher Topos Theory, Section 3.2.2, especially Definition 3.2.2.6 and Propositions 3.2.2.7–3.2.2.10; also Theorem 2.2.5.1 and Proposition 2.4.4.3 for the generic tools. During this repair the IAS URL timed out; I read the same source at https://people.math.harvard.edu/~lurie/papers/HTT.pdf, printed pp. 179–184 (PDF pages 197–202). Nothing was downloaded or written into the project. There is no Stacks tag for these quasicategorical results. The retained agent proof_origin explicitly identifies the blueprint ancestor and the unarchived HTT argument.

## Returned point and correction

The return is for reviewed branch head 712da5e48a: landing refused because the statement of lem-coef-cartesian-mapping-simplex-presentation changed after review. I compared every retained citation quotation against the current shared DAG, not just the named dependency. Exactly two quotations were stale, both to this presentation node (steps 2 and 6). Every other retained quotation was still verbatim.

The changed statement now points to lem-coef-joyal-model-structure for categorical equivalences and to lem-coef-marked-point-cartesian-model for the absolute marked model, and spells out that the natural marking on a vertex fiber marks its equivalences. I opened those current interfaces as well. The simplex formula, operators, degenerate-second-coordinate marking and vertex fibers are unchanged. Those are exactly the clauses used here; the item's argument does not invoke the presentation-existence theorem, the relative marked-equivalence conclusion, or the absolute marked-model reformulation. I replaced the two whole-statement quotations with the verbatim construction paragraph beginning “Let $n” and made this limited use explicit in the actual texts of steps 2 and 6. Thus the repaired node and citation evidence change substantively; this is not an unchanged re-push.

Rechecking the whole current DAG also found lem-coef-mapping-simplex-final-edge, created by Q94 while this delivery was in flight. Its self-contained formula for M, transition edge, arbitrary simplicial chains, source before the final fiber and strict enriched postcomposition conclusion agree with the retained proposed child. Step 4 now cites that existing statement and its quotation. Its generic tool use is declared in split_report.tool_uses. The duplicate unlanded child was removed, not renamed or edited in the shared DAG. The item's proof_deps is again exactly the union of its steps' uses.

The sandbox item also now carries the current base's audit metadata; deliver.py preserves maintainer fields from its freshly fetched origin base. The required --no-push delivery command performs the actual rebase onto that current DAG in its private worktree. No manual git command was run in the shared repository or sandbox.

## What was wrong in the source or route

The imported item agrees with HTT Proposition 3.2.2.7(2), with the three quasi-equivalence conditions of Definition 3.2.2.6 explicitly expanded. This repair makes no statement change, adds no hypothesis, and changes no conclusion. No STATEMENT-DISPUTED issue was found.

In the proof of HTT Proposition 3.2.2.10 (printed p. 183), the explanations for the initial and final restricted equivalences are interchanged: the initial part is the induction hypothesis; the final fiber is the assumed fiber equivalence. The retained steps 2–3 already assign these correctly. This is a source proof-label error, not an error in the theorem.

I read the recorded sec-smooth-purity chapter and sk-prop-sf-cbc unit, and the current main-20261015 thm-cbc-finite-level-proetale proof. The blueprint's opening compactification choice explains the ancestry of this auxiliary coherent-choice machinery; it does not supply the mapping-simplex theorem itself. The split remains below that node level, keeps the recorded blueprint ancestry and explicit from.place, and changes neither a chapter route nor a unit route. No unit file, target, coefficient category or exchange map was changed. No SGA source is used.

## What could not be finished

No mathematical repair remains open. The single new node intentionally remains statement-only for a later worker. The required server dry run via `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q19 lem-cbc-mapping-simplex-universal-equivalence --no-push .` completed successfully on 2026-10-17: `OK (not pushed) deliver/Q19/lem-cbc-mapping-simplex-universal-equivalence at dfcc3b0952: preflight passed`. This worker does not push; an independent second reader must inspect and deliver the repair.

## Not duplicates

lem-cbc-simplexwise-categorical-base-change vs lem-cbc-marked-mapping-simplex-descent: the new node tests underlying categorical equivalences after arbitrary simplicial base changes without marking or fibrancy assumptions. The existing node concerns relative marked cocartesian equivalences and a mapping-object consequence over a quasicategory.

lem-cbc-simplexwise-categorical-base-change vs lem-coef-sset-gluing-filtered-equivalences: the latter is about Kan weak homotopy equivalences, not Joyal categorical equivalences or universal pullback testing.

lem-cbc-simplexwise-categorical-base-change vs lem-coef-categorical-equivalences-small-generation: small generation does not assert the simplexwise universal-pullback criterion.

lem-cbc-simplexwise-categorical-base-change vs lem-coef-enriched-diagram-homotopy-descent: localization and pushout descent of enriched diagram categories do not state this assertion about simplicial base changes.

lem-cbc-simplexwise-categorical-base-change vs lem-cbc-mapping-simplex-universal-equivalence: the general locality theorem has no mapping simplex, cartesian fibration or fiberwise comparison hypothesis. The item still carries its dimension induction, initial/final-region decomposition and mixed mapping-set square before applying this locality result.

The repair repeated whole-DAG searches for 3.2.2.8 and 3.2.2.9 and the final-edge/simplexwise concepts, and whole-blueprint searches for “mapping simplex”, “simplexwise” and “final transition”. No blueprint node states the remaining child. Exact-source hits in operadic-colimit/section-colimit material have unrelated source numbering. The new existing final-edge node was reused as described above. There is no Stacks tag collision to distinguish.

## Mathlib search evidence

The actual msearch.py results from the first worker and independent second reader remain in searches.jsonl and the unchanged new node's mathlib_searches. They include LeanFinder, Loogle, Mathlib grep and LeanSearch, and a second semantic phrasing. I have not invented or rerun those records during this citation repair. The earlier readers recorded successful service responses and read the closest hits; zero-hit results are explicitly described as zero hits.

For the remaining child the searches include a simplexwise universal categorical-equivalence formulation and the broader over-category/representable/Joyal formulation. The closest hits concern ordinary fiber categories, simplicial subcomplexes, Kan-Quillen fibrations, or generic model-category constructions. The retained second-reader source inspection found that Mathlib/AlgebraicTopology/ModelCategory/Over.lean:90–105 tests only the underlying map for an over-category weak equivalence; it does not assert equivalences after every pullback. JoyalTrick.lean is a general lifting argument, not this categorical-equivalence theorem. None of the recorded hits supplies HTT 3.2.2.8 as an exact match or one-line specialization. This repair does not alter the searched statement or add any new node requiring another search record.

## Review by Q19

This is the repair worker's review of the retained delivery against the current interfaces. I read delivery-errors B–E in full, the worker and stage-1 contracts, GOAL, dag-sync, SETUP's three blueprint levels, the chapter/unit records, the current blueprint ancestor, the entire retained proof, both retained child statements, and the current statement of every node cited in its proof. I opened the changed presentation statement and its newly explicit definition references. I independently read HTT's definition/construction and complete statements and proofs of 3.2.2.8–3.2.2.10 using the Harvard PDF.

1. Step 1: coherent-nerve-comparison supplies the object-preserving locally Kan replacement, Quillen equivalence and composition-compatible mapping comparison. joyal-quasicategory-characterizations supplies the quasi-inverse characterization; enhanced-functor-cone-calculus supplies mapping equivalences induced by a functor equivalence. infinity-cocartesian-mapping-criterion supplies the exact homotopy-pullback mapping square after reversing horns. I checked the dual variance, the subset reversal and the fact that both base interval-subset posets have a least element. This proves the enriched postcomposition equivalence for a cartesian edge over r−1 to r, with the incoming source before r. No fibrancy of unreplaced enriched mapping sets is asserted.

2. Step 2: infinity-fibrations gives the actual horn and lift conditions. The current presentation statement gives exactly the simplex formula, markings and vertex fibers used in restriction. Pairing prescribed base simplices with horn fillers verifies the initial-face pullback is a cartesian fibration; filling inner horns in the simplex verifies its total space is a quasicategory. The induction is explicitly stated before use and begins with the fiber assumption in dimension zero. The final restricted equivalence is the original fiber hypothesis, not the induction. The expanded text now explicitly limits the presentation citation to its construction clauses.

3. Step 3: coherent-nerve-comparison gives the realization by simplex colimits, subset mapping sets and union composition. The written monotone-generator argument verifies that the initial and final enriched subcategories are full and the reverse mixed mapping sets are empty. rigidification-equivalence-detection applies to the two restricted categorical equivalences and gives precisely their local weak equivalences and essential surjectivity. No fully-faithfulness theorem is taken merely from a definition.

4. Step 4: I compared the entire current lem-coef-mapping-simplex-final-edge statement to HTT 3.2.2.9 and to the removed duplicate. Its M formula is the same construction, its e is represented by the same s_0y, and its x lies strictly before the final fiber. It supplies exactly the upper horizontal weak equivalence. The left vertical is step 3; the bottom horizontal is step 1 because the marked-edge hypothesis makes q(e) cartesian. Functorial composition makes the square commute and the stated component/homotopy-group argument gives the remaining side. No new hypothesis on any A_i is introduced.

5. Step 5: coherent-nerve-comparison's Dwyer–Kan definition and rigidification-equivalence-detection say exactly what this step uses. Same-region, forward mixed and empty reverse mixed cases exhaust all mapping pairs. Essential surjectivity holds region by region, so the detection theorem completes the dimension induction before any universal pullback assertion is used.

6. Step 6: the current presentation's explicit operators identify the pullback along any monotone alpha with the chain A_alpha(j), including repetitions and identity transitions. The marking formula is unchanged under this identification. infinity-fibrations verifies cartesian lifts and inner/outer horn fillers by pairing with the given base simplex. Thus the completed induction applies to every simplex pullback; it does not assume arbitrary pullback stability of categorical equivalences. The citation now quotes only these construction clauses.

7. Step 7: the remaining new lemma states exactly the simplexwise-to-all-base-changes implication needed after step 6, for arbitrary small simplicial sets. Its hypotheses do not require T or the fibers to be quasicategories. Empty T gives two empty pullbacks. For n=0 the completed induction handles every constant simplex map; there is no appeal to unproved right properness.

For the remaining child, HTT 3.2.2.8 has the same arbitrary diagram and both implications, with no omitted fibration condition. I checked the empty base (forcing all input objects empty), empty test object, and point-base cases; over a point the hypothesis still tests every simplex product. It is a substantive locality theorem, not an elementary step or a clause moved out of this item: its source uses finite-cell induction, homotopy pushouts and filtered colimits. B1–B9 were checked: statement only, all objects and universes introduced, definition citations present, single-escaped TeX, exact non-Stacks source honestly identified, searched no-match rather than a spurious Mathlib leaf, no source number used to define meaning, and filled blueprint ancestry. The Lean attachment searches found nothing.

C1/C4 were rechecked against the actual current statements for all 14 citation pairs; citations.json covers precisely the uses lists and every quote is verbatim. The only changed retained statement was the presentation node. The new reused final-edge statement was read independently, not inferred from its title. The two elementary steps are the explicit restriction and simplex-pullback computations, with their lifting arguments written out. No existing proof is used beyond the cited statements. D1–D5 pass because the item retains the substantive induction and mixed square; the new child is an independent locality result. E1–E7 checks include smallness, variance, noninjective simplices, non-Kan enriched mapping sets, empty fibers and the source's swapped explanation labels. A nonempty final fiber cannot transition into an empty penultimate fiber, and with point fibers in dimension one the mapping calculation reduces to maps of points. No outstanding statement dispute or prohibited source remains.

## Repair dry-run history

The first repair dry run reached server preflight after waiting for worktree/fetch capacity. It failed because HEAD was no longer atop origin/newtargets-dag and the resulting comparison included unrelated coord/blueprint-index.tsv. Neither is a sandbox file or mathematical citation failure. I left the repaired item intact and reran the authorized delivery tool to rebuild on a fresh fetched base. The second run completed with `OK (not pushed) deliver/Q19/lem-cbc-mapping-simplex-universal-equivalence at dfcc3b0952: preflight passed`; I did not work around the tool or edit the shared index.

## Second reading by Q19

- Item statement: checked against HTT Definition 3.2.2.6 and Proposition 3.2.2.7(2), pp. 180–181; all hypotheses, arbitrary $T\to\Delta^n$, empty cases, and the conclusion agree.
- New node `lem-cbc-simplexwise-categorical-base-change`: checked against HTT Proposition 3.2.2.8, p. 181; the two equivalent conditions and unrestricted simplicial-set hypotheses agree.
- Step 1: checked against HTT Proposition 2.4.4.3 and the cited coherent-nerve, quasicategory, cone-calculus, and cocartesian-mapping statements; opposite dualization gives the required postcomposition equivalence with the stated variance.
- Step 2: checked against HTT Proposition 3.2.2.10, pp. 183–184, and the current fibration and mapping-simplex interfaces; the induction, initial restriction, and final-fiber use are correctly separated.
- Step 3: checked against the current coherent-realization and rigidification statements and HTT’s two-region decomposition; fullness, empty reverse mapping sets, and Dwyer–Kan data are all supplied.
- Step 4: checked against HTT Lemma 3.2.2.9 and the current `lem-coef-mapping-simplex-final-edge` statement; the mixed square has the correct edge, source region, and cartesian bottom map.
- Step 5: checked against HTT Proposition 3.2.2.10 and the cited detection statements; same-region, forward mixed, and empty reverse cases exhaust the mapping sets.
- Step 6: checked against HTT Remark 3.2.2.2 and the paragraph after Proposition 3.2.2.8; the degreewise pullback formula handles repeated vertices and identity transitions, and the cartesian-fibration hypotheses are preserved.
- Step 7: checked against HTT Propositions 3.2.2.7(2) and 3.2.2.8; it applies the simplexwise criterion exactly and treats empty $T$, $n=0$, empty fibers, and arbitrary universes.
- Citation audit: all 14 step/node quotations were checked verbatim against the current DAG statements; each `uses` entry has exactly one sufficiently long quote.
- Mathlib audit: the new node has recorded grep, LeanFinder, LeanSearch, and Loogle searches; no declaration states the result. Additional independent searches found only generic over-category, Cech-nerve, and model-category declarations.
- Duplicate audit: the removed `lem-cbc-mapping-simplex-last-edge-composition` is subsumed by existing `lem-coef-mapping-simplex-final-edge`; the retained simplexwise node is a distinct general locality theorem.
- Small-case audit: checked zero and empty simplicial sets, point fibers, $n=0$ and $n=1$, constant and noninjective simplex maps, and empty test bases; no counterexample or missing hypothesis was found.
- Changes: no mathematical statements changed; the existing final-edge node is cited in step 4, the duplicate child remains removed, and this second-reading record plus independent search evidence were added. The required dry run passed on the server.
