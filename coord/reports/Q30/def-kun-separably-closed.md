# Q30: def-kun-separably-closed

## Files written

- dag/nodes/sec-curve-estimates/def-kun-separably-closed.json: definition; Mathlib leaf, `IsSepClosed` (Mathlib/FieldTheory/IsSepClosed.lean:66) and `IsSepClosure` (same file:227). Zero new nodes; one item becomes a Mathlib leaf.
- citations.json: empty list, since this definition/Mathlib leaf has no proof steps and hence no proof-step citations.
- report.md: this report. searches.jsonl is the search command's own log.

## Attachments

None for the whole item. I searched the project library both for its blueprint tag and for its notions. `IsSepClosed.iff_forall_finrank_eq_one`, WeilConjectures/Mathlib/FieldTheory/IsSepClosed.lean:131, proves the equivalent finite-extension characterization, and `IsSepClosed.iff_exists_root`, line 109, proves the root characterization. Neither defines a separable closure, so neither states every clause of this item. The two relevant classes are Mathlib declarations and therefore are reported as a leaf, not as a project attachment. The existing stage-2 lean record already names both classes and is retained unchanged.

## WANTED

None.

## What changed and why

I read the imported source, its `blueprint_update`, and the current source literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-sf-comparison/def-kun-separably-closed.md. Following that update, the polynomial-splitting formulation is now primary; the equivalent finite-separable-extension formulation and the entire separable-closure clause remain. This is alignment with the explicitly supplied current blueprint, not a disputed or weakened statement. I spelled out splitting inline (including constant polynomials) and cited the actual existing definition nodes for the remaining notions. The old dependency on scheme conventions was unused: the item is wholly field-theoretic. No hypotheses, existence assertion, chosen closure, perfectness assumption, or characteristic restriction were added.

The sources, kind, chapter, unit, Lean records, import flags, and blueprint metadata are retained. `blueprint.from` remains null as required for an imported node. `same_as` is [] for the complete two-clause statement; the partial overlaps are discussed below. The item is not the unit's key theorem and changes no unit or chapter file.

## Not duplicates

No new nodes were created. Whole-DAG and whole-blueprint searches for “separably closed” and “separable closure” found these relevant partial overlaps:

- def-kun-separably-closed vs def-pc-separably-closed: the Picard node defines separably closed fields in root form, but does not include the definition of a separable closure. It is not equivalent to this entire two-clause item.
- def-kun-separably-closed vs def-pd-separable-closure: that node defines a separable closure but also asserts the filtered-colimit presentation, faithful flatness, and fixes a closure and base-change convention. This item merely defines the two predicates and asserts none of those extra properties.
- def-kun-separably-closed vs def-weil-pbc-separable-algebraic-extension: the latter defines separable algebraic extensions in general, with no separably closed top-field requirement. It is reused as a statement dependency.

## Review by Q30

I read the current blueprint's two sentences against the pinned Mathlib source, not just search summaries. In Mathlib/FieldTheory/IsSepClosed.lean:66-67, `IsSepClosed K` requires exactly that each separable polynomial over K splits. In lines 227-229, `IsSepClosure K L` has precisely a separably closed top field L and `Algebra.IsSeparable K L`; `isSepClosure_iff` at lines 258-260 confirms this conjunction. I then read Mathlib/FieldTheory/Separable.lean:539-572: its element predicate is separability of the minimal polynomial, and its class requires that of every element; the instance at 570 supplies algebraicity over a nontrivial base. A field is nontrivial, so the item has every hypothesis of that instance and its explicit algebraicity clause is automatic, rather than a missing Mathlib condition.

For the parenthetical characterization, I checked `IsSepClosed.algebraMap_bijective` at Mathlib/FieldTheory/IsSepClosed.lean:211-213: it applies to separable extensions, even without finiteness, and gives exactly triviality of the extension map. I also read the complete project proof of `IsSepClosed.iff_forall_finrank_eq_one` at WeilConjectures/Mathlib/FieldTheory/IsSepClosed.lean:131-148. Its converse takes a root of an irreducible separable polynomial in an algebraic closure, forms the finite separable simple subextension, and applies the degree-one hypothesis. This verifies the current blueprint's parenthesis without changing the operative polynomial definition or claiming that the existing node `lem-pc-sepclosed-finite-sep-trivial` proves a converse it does not state. No proof-step citation of that node is made.

I opened and read the statements of every statement dependency: `def-weil-field` supplies fields, `def-weil-polynomial-ring` the polynomial ring, `def-pc-separable-polynomial` the separability predicate, `def-pc-field-tower` finite separable extensions, `def-pc-field-extension` field extensions, and `def-weil-pbc-separable-algebraic-extension` exactly the separable algebraic condition in the closure clause. This leaf has no numbered proof steps, so the C1/C4 quote obligations are empty; citations.json records that explicitly. I checked B through E of delivery-errors: no new unproved lemma, relabelling split, off-route theorem, circular definition, or hidden long argument was introduced. All search entries added today come from actual msearch.py runs with exactly their logged query text. One grep against a single file misparsed line numbers as filenames; a subsequent directory grep gave correct file-and-line pairs, which I verified by reading the files. All search services used returned results.

As small cases, a nonzero constant is separable and splits via the empty product, whereas zero is not separable; this avoids accidentally demanding roots of constants. An algebraically closed field satisfies the polynomial definition. A finite field F_q fails it: T^q-T-1 has derivative -1 and no root in F_q. A separably closed field is its own separable closure, consistent with `IsSepClosure.self_of_isSepClosed` at line 232. I specifically checked that no algebraic-closedness or perfectness requirement is imposed: separable closure is not algebraic closure in positive characteristic for an imperfect base. The algebraicity instance uses only the field/nontrivial and separability hypotheses already present.

## Unfinished work

None. No Lean writing, compiler, Lake, global build, repository writes, launcher edits, or sub-agents were used. The required server dry run and delivery are the remaining operational checks.

## Delivery blocker

The standalone server review_split passed: `def-kun-separably-closed: PASS; 0 new nodes; the item is a Mathlib leaf`.

The required full dry run exited 1 and pushed nothing. Its sole failure was:

```
deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps
```

I opened the existing repository node dag/nodes/sec-smooth-purity/lem-kun-proper-torsion-cd-bound.json: its fourth proof step already has `def-kun-separably-closed` in `uses`, but its `proof_deps` omits that id. My sandbox contains only the assigned item and does not change that node. The existing defect is selected by tools/dag_delta.py `introduced` because it treats a dependency diagnostic mentioning a delivered id as blocking even when the same diagnostic exists on the baseline. That node requires a maintainer correction (at least synchronizing its proof_deps with its step uses), or a maintainer decision on the gate's attribution. The brief forbids editing another worker's node or patching/bypassing the gate. I therefore made no such edit, launched no push, and report BLOCKED with the completed leaf and report retained for reuse. No deliver.py invocation remains active.

## Resumed dry run (2026-10-21)

Resumed the retained item and report and ran the required dry run first: `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push .`. It completed with exit code 1 after server preflight and again reported the sole dependency diagnostic quoted above. Nothing was pushed. I reread the current repository node: its fourth step still uses `def-kun-separably-closed` and its `proof_deps` still omits that id. The retained item's `blueprint_update` and existing Lean record still match the current repository. No search was repeated, no other worker's node or launcher file was changed, and the required dry run process has exited. Delivery remains blocked by the existing out-of-scope dependency defect.

## Latest resumed dry run (2026-10-21)

The next resumed attempt retained the existing item, report, citations, and search log. I ran the required full dry run before making any changes to the split. The invocation exited 1 after admission to server preflight, with the same sole failure: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. No delivery command remains active and nothing was pushed.

I compared the retained item with the current read-only repository: its unchanged metadata, current `blueprint_update`, and existing Mathlib Lean record agree. I reread the current blueprint, both Mathlib classes, the separability-to-algebraicity instance, the project finite-extension equivalence, all six statement dependencies, and the recorded search results. These still support the retained Mathlib leaf, without another search or mathematical change. The existing proper-torsion-bound node still lists this item in step 4's `uses` but omits it from `proof_deps`. Correcting it would edit another worker's node, which the brief expressly forbids; changing or bypassing the delivery gate is likewise forbidden. The blocker therefore persists outside this item's authorized edit scope. Only this sandbox report was updated.

## Dispatcher retry at 2026-10-21T04:23:23+00:00

Retained the item, report, citations and logged searches. The required first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, exited 1 with the same sole server preflight failure: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; no push was attempted.

I compared the retained item with the current repository: source, chapter, unit, blueprint_update, lean and reviewed_lean match. I reopened the current blueprint and Mathlib's IsSepClosed, IsSepClosure, isSepClosure_iff and separability-to-algebraicity instance; these continue to support the retained leaf. I read the recorded search results without repeating queries. The current proper-torsion-bound node still contains the item in step 4's uses but not in proof_deps, confirming the preflight diagnostic on an existing node. Stage 1 section 2 forbids changing another node, and the direct-delivery brief forbids patching or bypassing launcher gates. Consequently the external dependency defect cannot be repaired within this item's scope. Only this report was updated; the complete retained leaf remains ready for retry after a maintainer correction.

## Dispatcher final retry at 2026-10-21T04:27:10+00:00

Retained all previous work and search results. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push .`, completed with exit code 1. Server preflight again reported exactly one blocking finding: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The invocation has exited; no push was attempted.

I checked the current read-only repository directly: that existing node's fourth step does contain this item in `uses`, while its `proof_deps` omits it. My sandbox still contains only the assigned item node. Its source, chapter, unit, blueprint_update, lean and reviewed_lean records agree with the current repository. I reopened the current blueprint's two definition sentences, Mathlib's `IsSepClosed` (66–67), `IsSepClosure` (227–229), `isSepClosure_iff` (258–260), and `Algebra.IsSeparable.isAlgebraic` (Separable.lean:570–572); they continue to support the retained leaf. No mathematical or search changes were needed.

The necessary correction is outside the permitted item: the brief forbids editing another worker's node and forbids patching or bypassing the delivery gate. Therefore delivery remains BLOCKED by the existing dependency metadata defect. Only this sandbox report was updated; item, citations and searches are retained unchanged.


## Dispatcher final retry at 2026-10-21T04:31:24+00:00

The mandatory dry run was rerun after retaining the current item and search log. `deliver.py Q30 def-kun-separably-closed --no-push .` exited 1 during server preflight with the same sole finding: `lem-kun-proper-torsion-cd-bound` step 4 uses `def-kun-separably-closed`, but that id is absent from its `proof_deps`. The independent server `srvcheck.py ... check_dag` immediately reproduced the same finding. No push occurred. The sandbox item remains a complete Mathlib leaf; fixing the cited node would violate the brief's prohibition on editing another worker's node, so delivery remains blocked outside this item's scope.

## Final dispatcher retry at 2026-10-21T04:36:09+00:00

I reran the required dry run first, retaining the item, citations, and logged searches. `deliver.py Q30 def-kun-separably-closed --no-push .` exited 1 during server preflight with the same single finding: `lem-kun-proper-torsion-cd-bound` step 4 uses `def-kun-separably-closed`, but the id is absent from that node's `proof_deps`. The required independent `srvcheck.py ... check_dag` also exited 1 with that finding. No push occurred. The defect is in another worker's node and cannot be repaired in this sandbox under the direct-delivery brief.

## Dispatcher retry at 2026-10-21T05:46:43+00:00

Retained the existing item, report, citations and recorded search results. The required first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, completed with exit code 1 and the same sole preflight finding: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited and no push was attempted.

I compared the sandbox item with the current repository: source, chapter, unit, blueprint_update, lean and reviewed_lean remain unchanged. I reopened the current blueprint, Mathlib IsSepClosed and IsSepClosure definitions, isSepClosure_iff, the separability-to-algebraicity instance, and the project finite-extension characterization. The retained Mathlib leaf still matches both definition clauses. I read the previous searches and their results without repeating them. I also reopened the existing proper-torsion-bound node: step 4 contains this item in uses and its proof_deps omits it, confirming the diagnostic. Repairing that node or bypassing the gate is outside the permitted scope. Only this sandbox report was updated; delivery remains blocked pending a maintainer correction.

## Dispatcher retry at 2026-10-21T05:49:17+00:00

Retained the existing item, citations, report and all logged search results. The required first dry run (`deliver.py Q30 def-kun-separably-closed --no-push`) completed with exit code 1 and the same sole server preflight failure: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. No delivery process remains active and no push was attempted.

I reread the current blueprint's two definition clauses, Mathlib's IsSepClosed and IsSepClosure classes, isSepClosure_iff, the separability-to-algebraicity instance, the project finite-extension equivalence, all six statement dependencies, and the retained search log. These continue to support the existing Mathlib leaf. The item's source, chapter, unit, blueprint_update, Lean records and import flags match the current repository. I also confirmed directly that the external node lists this item in step 4's uses but omits it from proof_deps. The sandbox contains just the assigned item node. Repairing the external node or bypassing the gate is forbidden by the direct-delivery brief. Only this report was updated; the complete retained leaf remains blocked pending the maintainer's metadata correction.

## Dispatcher retry at 2026-10-21T05:50:56+00:00

Retained the existing item, report, citations and search log. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, completed with exit code 1 after server preflight admission. Its sole failure remains: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The invocation has exited and no push was attempted.

I compared the retained item to the current repository: source, chapter, unit, blueprint_update, lean, reviewed_lean and import_flags match. I reread the current blueprint, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, the separability-to-algebraicity instance, all six statement dependencies, and the retained search results. They continue to support the retained leaf without new searches or mathematical changes. I directly inspected the external node and confirmed that its fourth proof step cites this item while proof_deps omits it. The brief forbids edits to another worker's node or modifications/bypasses of launcher gates; a maintainer correction is required. Only this sandbox report was updated.

## Dispatcher retry at 2026-10-21T05:53:08+00:00

Retained the existing item, report, citations and logged search results. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push .`, exited 1 after server preflight admission with exactly one finding: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

I directly inspected the current repository node at `dag/nodes/sec-smooth-purity/lem-kun-proper-torsion-cd-bound.json`: its fourth step cites this item and its proof_deps omits it. I compared the retained item with the current repository; the changed fields are still precisely statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint and split_report. I reopened the current blueprint definition and Mathlib's IsSepClosed, IsSepClosure, isSepClosure_iff and separability-to-algebraicity instance, together with the project's finite-extension characterization. They continue to support the retained Mathlib leaf. No new search or mathematical change was needed. The delivery failure concerns another worker's node, which this brief forbids editing, and patching or bypassing the delivery gate is forbidden. Only this report was updated; delivery remains blocked pending the maintainer's metadata correction.


## Dispatcher retry at 2026-10-21T05:56:27+00:00

Retained the existing item, report, citations and logged searches. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push .`, exited 1 during server preflight with one finding: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The independent server `srvcheck.py weil-conjectures-sheaf Q30 def-kun-separably-closed check_dag` also exited 1 with the same finding. Both processes have exited; nothing was pushed.

I compared the retained item with the current repository: only statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint and split_report differ. I reopened the current blueprint's two definition sentences, the Mathlib IsSepClosed and IsSepClosure definitions, isSepClosure_iff and Algebra.IsSeparable.isAlgebraic, and read all six statement dependencies. These still support the retained Mathlib leaf. The existing search results are retained without repeating queries. I directly inspected the external node: its fourth proof step cites this item, while its proof_deps omits it. Repairing that node is prohibited by the direct-delivery brief; patching or bypassing the gate is likewise prohibited. Only this sandbox report was updated. Delivery remains blocked pending a maintainer correction of the external dependency metadata.

## Dispatcher retry at 2026-10-21T05:58:25+00:00

Retained the item, citations, report and actual search log. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push .`, exited 1 after server preflight admission with exactly one failure: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The invocation has exited; nothing was pushed.

I compared the retained item with the current repository: the only changed fields remain statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint and split_report. I read the current blueprint definition, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, Algebra.IsSeparable.isAlgebraic, the project finite-extension characterization, and all six statement-dependency statements. They continue to support the retained leaf. The recorded search results were read and preserved without repeating searches. The sandbox still contains only the assigned item node.

I directly verified the external node: step 4 includes this item in uses, while proof_deps omits it. The correction is to another worker's node, which the brief and stages/1-dag.md section 2 forbid me to edit. Launcher/gate modifications and bypasses are also forbidden. Therefore the failed preflight cannot be repaired within this item's authorized scope. Only this sandbox report was updated; delivery remains blocked pending a maintainer correction of the external dependency metadata.

## Dispatcher retry at 2026-10-21T06:00:06+00:00

Retained the item, citations, report and logged search results. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, exited 1 with exactly one preflight finding: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited and nothing was pushed.

I directly checked the current external node: its fourth proof step includes this item in uses, and proof_deps omits it. The retained item differs from the current repository only in statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint and split_report. I reread the chapter and unit, current blueprint definition, Mathlib IsSepClosed and IsSepClosure classes, isSepClosure_iff, the separability-to-algebraicity instance, the project finite-extension characterization and all six statement-dependency statements. The retained Mathlib leaf remains supported; no mathematical change or repeated search was needed. A fresh project-source search found neither the blueprint tag nor a project definition of either entire notion. The complete prior search results remain recorded.

The preflight blocker requires editing another worker's existing node, which stages/1-dag.md section 2 and the direct-delivery brief forbid. Patching or bypassing the gate is also forbidden. Only this sandbox report was updated; delivery remains blocked pending a maintainer correction of the external dependency metadata.


## Dispatcher retry at 2026-10-21T06:01:38+00:00

Retained the existing item, report, citations, and logged search results. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, exited 1 after server preflight admission with exactly one finding: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

I directly checked the current external node: its fourth proof step includes this item in uses, while proof_deps omits it. The retained item differs from the current repository only in statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint, and split_report. I reread the current blueprint definition, the chapter and unit, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, the separability-to-algebraicity instance, the project finite-extension characterization, all six statement-dependency statements, and the retained search results. These continue to support the existing Mathlib leaf. A project-source search found no declaration of the entire two-clause item. No search or mathematical change was necessary.

The required correction is to another worker's node, which this brief forbids editing. Patching or bypassing the delivery gate is also forbidden. Only this sandbox report was updated; the complete leaf remains retained pending a maintainer correction of the external dependency metadata.


## Dispatcher retry at 2026-10-21T06:02:52+00:00

Retained the existing item, citations, report, and search log. The required first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push .`, completed with exit code 1 after server preflight admission. Its sole finding remains: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

I directly opened the current external node and verified the missing dependency in its proof_deps alongside the citation in step 4. I compared the retained item with the current repository: only status, split_report, stmt_deps, mathlib_match, statement, blueprint, and mathlib_searches differ. I reread the chapter, unit, all six statement-dependency statements, current blueprint definition, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, the separability-to-algebraicity instance, and the project's finite-extension characterization. These still support both clauses of the retained Mathlib leaf. I read the actual search log and results without repeating queries. The project-source search supplied no entire-item attachment; no mathematical changes were needed.

The failure requires a correction to another worker's existing node, which stages/1-dag.md section 2 and the direct-delivery brief forbid me to edit. The brief also forbids patching or bypassing launcher gates. Only this sandbox report was updated. The complete leaf remains retained pending the maintainer's correction of the external dependency metadata.


## Dispatcher retry at 2026-10-21T06:04:08+00:00

Retained the item, citations and all recorded search results. The required first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, completed with exit code 1. Its sole preflight failure was: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

I directly reopened that current repository node: step 4 lists this item in `uses`, while `proof_deps` omits it. The sandbox changes only the assigned node, and its differences from the current repository remain statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint and split_report. The current blueprint still supplies both retained definition clauses; the Mathlib and project source checks and recorded searches do not require a change to this leaf. No searches were repeated. Repair requires changing another worker's node, expressly forbidden by the direct-delivery brief. Patching or bypassing the gate is also forbidden. Only this sandbox report was updated; delivery remains blocked pending the maintainer's correction of the external dependency metadata.


## Dispatcher retry at 2026-10-21T06:05:50+00:00

Retained the item, citations, report and all logged searches. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, exited 1 after server preflight admission with exactly one blocking finding: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The command has exited; nothing was pushed.

I compared the retained item with the current repository and checked the current blueprint, both Mathlib classes and isSepClosure_iff, the separability-to-algebraicity instance, and the complete project finite-extension characterization. I read the retained search results without rerunning unchanged queries and reopened all six statement dependencies. The retained item remains a Mathlib leaf for both definition clauses; no mathematical repair or new node is needed. The existing external node still cites the item in step 4 while omitting it from proof_deps. The direct-delivery brief forbids editing another worker's node and forbids patching or bypassing launcher gates. The required correction therefore remains outside this worker's authorized scope. Only this sandbox report was updated.


## Dispatcher retry at 2026-10-21T06:07:16+00:00

Retained the existing item, citations, report, and logged search results. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, exited 1 after server preflight admission with exactly one failure: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

I compared the retained item with the current read-only repository: the only changed fields remain statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint, and split_report. I read the chapter/unit records, current blueprint's two definition clauses, the pinned Mathlib classes IsSepClosed and IsSepClosure, isSepClosure_iff and Algebra.IsSeparable.isAlgebraic, the project finite-extension characterization, all six statement-dependency statements, and the recorded searches. They continue to support the retained Mathlib leaf; the project-source search supplied no entire-item attachment. No mathematical change or repeated query was needed.

I directly confirmed the external node's fourth step lists this item in uses while its proof_deps omits it. The sandbox contains only the assigned item node. The direct-delivery brief forbids editing another worker's node or patching/bypassing launcher gates, so this failure requires a maintainer correction outside this item's authorized scope. Only this sandbox report was updated.


## Dispatcher retry at 2026-10-21T06:09:29+00:00

Retained the existing item, citations, report and logged searches. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, completed with exit code 1 after server preflight admission. Its sole finding is still: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The command has exited; nothing was pushed.

I compared the retained item with the current repository: the differing fields remain blueprint, mathlib_match, status, stmt_deps, statement, mathlib_searches and split_report. The sandbox contains only the assigned item node. I reread the current blueprint's two definition sentences and the retained review and search descriptions, and searched the project source for the blueprint tag and the relevant definitions and characterizations; no whole-item project attachment appeared. No mathematical or search change was made.

I directly confirmed the external node's fourth step cites this item while its proof_deps omits it. Correcting another worker's node is expressly forbidden by the direct-delivery brief and stages/1-dag.md section 2; modifying or bypassing the launcher gate is likewise forbidden. This preflight failure therefore requires a maintainer correction outside this item's authorized scope. Only this sandbox report was updated.


## Dispatcher retry at 2026-10-21T06:13:42+00:00

Retained the item, report, citations, and recorded search results. The mandatory first dry run (`python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`) completed with exit code 1 after server preflight admission. Its sole failure remains: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The invocation has exited; nothing was pushed.

I compared the retained item against the current repository and read its chapter, unit, current blueprint, both Mathlib classes, isSepClosure_iff, the separability-to-algebraicity instance, the project finite-extension characterization, all six statement dependencies, and the retained search log. They still support the complete two-clause Mathlib leaf; no mathematical change or repeated search was needed. I directly confirmed the external node has this item in step 4 uses but not in proof_deps. The direct-delivery brief and stages/1-dag.md forbid editing another worker's node, and launcher modifications or gate bypasses are expressly forbidden. The required maintainer correction is outside this sandbox's authorized scope. Only this report was updated.


## Dispatcher retry at 2026-10-21T06:16:25+00:00

Retained the item, citations, report and actual search log. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, completed with exit code 1 after server preflight admission. Its sole finding remains: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

I compared the sandbox item with the current repository: only blueprint, status, split_report, stmt_deps, mathlib_searches, mathlib_match and statement differ. I reread the chapter and unit, current blueprint definition, all six statement dependencies, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, Algebra.IsSeparable.isAlgebraic, and the complete project finite-extension characterization. Both clauses of the retained Mathlib leaf remain supported. The project-source search found no declaration of the entire item. I read the recorded searches and results without repeating unchanged queries, and checked delivery-errors B through E; no mathematical repair or new node is needed.

I directly confirmed that the external node cites this item in step 4 while omitting it from proof_deps. The direct-delivery brief expressly forbids editing another worker's node or modifying/bypassing launcher gates. The necessary correction is therefore outside this item's authorized scope and requires the maintainer. Only this sandbox report was updated; all retained work remains available.


## Dispatcher retry at 2026-10-21T06:20:38+00:00

Retained the completed item, report, citations, and actual search log. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, exited 1 after server preflight with exactly one finding: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

I compared the retained item with the current repository: only statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint, and split_report differ. I read the current blueprint definition, the chapter and unit, all six statement dependencies, the recorded search results, and Mathlib's IsSepClosed, IsSepClosure, isSepClosure_iff and Algebra.IsSeparable.isAlgebraic declarations. They continue to support the retained leaf. A fresh project-source search found the partial root and finite-extension characterizations, but no definition covering the whole two-clause item. No mathematical change or repeated Mathlib search was needed.

I directly confirmed the external node's fourth step includes this item in uses while its proof_deps omits it. Stage 1 section 2 and the direct-delivery brief forbid changing another worker's node; the brief also forbids patching or bypassing the gate. The required maintainer correction is therefore outside this item's authorized scope. Only this sandbox report was updated. Delivery remains blocked by the external dependency metadata defect.


## Dispatcher retry at 2026-10-21T06:29:42+00:00

Retained the completed item, report, citations and recorded search results. The required first dry run (`python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push .`) exited 1 with exactly one preflight failure: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The independent server `srvcheck.py weil-conjectures-sheaf Q30 def-kun-separably-closed check_dag` also exited 1 with the same finding. Both processes have exited; nothing was pushed.

I compared the sandbox item against the current repository and reread the chapter/unit records, current blueprint definition, all six statement dependencies, the actual logged searches, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, Algebra.IsSeparable.isAlgebraic, and the project's finite-extension characterization. These still support both clauses of the retained Mathlib leaf. The project-source tag search found no whole-item attachment. The differing fields remain statement, blueprint, split_report, stmt_deps, status, mathlib_match and mathlib_searches; no mathematical change or repeated search was needed.

I directly confirmed that the external proper-torsion-bound node lists this item in step 4 uses while omitting it from proof_deps. The direct-delivery brief and stages/1-dag.md section 2 forbid changing another worker's node; launcher changes and gate bypasses are also forbidden. The required correction therefore belongs to the maintainer, outside this item's authorized scope. Only this sandbox report was updated.


## Dispatcher retry at 2026-10-21T06:31:55+00:00

Retained the existing item, report, citations and recorded search results. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, completed with exit code 1 after server preflight admission. Its sole failure remains: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The invocation has exited; nothing was pushed.

I compared the retained item with the current read-only repository and read the current blueprint definition, chapter/unit records, statement dependencies, logged searches, Mathlib IsSepClosed and IsSepClosure classes, isSepClosure_iff, Algebra.IsSeparable.isAlgebraic, and the project finite-extension characterization. Both definition clauses remain supported, and project-source searches found no whole-item attachment. No new search or mathematical change was needed.

I directly verified the external node's fourth step includes this item in uses while proof_deps omits it. Correcting that existing node is expressly forbidden by the direct-delivery brief; patching or bypassing launcher gates is also forbidden. The necessary repair is outside this item's authorized scope and requires the maintainer to synchronize that node's proof_deps with its proof-step uses. Only this sandbox report was updated.


## Dispatcher retry at 2026-10-21T06:34:18+00:00

Retained the completed item, citations, report, and actual search log. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, completed with exit code 1 after server preflight admission. Its sole failure remains: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The invocation has exited; nothing was pushed.

I compared the sandbox item against the current repository: the only differing fields remain statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint, and split_report. I read the chapter and unit records, current blueprint definition, both Mathlib classes, isSepClosure_iff, Algebra.IsSeparable.isAlgebraic, the project finite-extension characterization, all six statement dependencies, and the retained search log. These still support both clauses of the retained Mathlib leaf. Project-source searches found no declaration covering the entire item. No mathematical change or repeated Mathlib search was needed.

I directly confirmed that the external proper-torsion-bound node cites this item in its fourth step but omits it from proof_deps. The direct-delivery brief and stage-1 rules prohibit changing another worker's node; launcher modifications and gate bypasses are also forbidden. The needed correction therefore remains outside this worker's authorized scope. Only this sandbox report was updated, and all retained work remains available.


## Dispatcher retry at 2026-10-21T06:38:16+00:00

Retained the existing item, report, citations and actual search log. The required first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, completed with exit code 1 after server preflight admission. Its sole failure remains: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

I compared the retained item with the current read-only repository: only statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint and split_report differ. I read the chapter and unit, all six statement-dependency statements, the current blueprint definition, the actual logged searches, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, Algebra.IsSeparable.isAlgebraic, and the complete project finite-extension characterization. These still support both clauses of the retained Mathlib leaf. The project-source searches found no declaration covering the whole item. Delivery-errors B through E require no mathematical repair or new node here. Unchanged search questions were not repeated.

I directly confirmed that the existing external proper-torsion-bound node cites this item in its fourth step but omits it from proof_deps. Correcting that existing node is expressly forbidden by this direct-delivery brief and stages/1-dag.md section 2. Launcher modifications and gate bypasses are also forbidden. A maintainer must synchronize that node's proof_deps with its step uses; this correction is outside the authorized sandbox item. Only this sandbox report was updated, and all retained work remains available.


## Dispatcher retry at 2026-10-21T06:41:45+00:00

Retained the completed item, report, citations and actual search log. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push .`, completed with exit code 1 after admission to server preflight (slot 9). Its sole finding was `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The invocation has exited; nothing was pushed.

I directly inspected the current external node and confirmed that step 4 includes this item in uses while proof_deps omits it. The retained item differs from the repository only in statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint and split_report. I read the current blueprint definition, chapter and unit records, all six statement dependencies, the recorded search results, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, Algebra.IsSeparable.isAlgebraic, and the project finite-extension characterization. Both clauses remain supported by the existing Mathlib leaf; the project declarations cover only partial characterizations. Delivery-errors B through E require no mathematical repair or new node for this definition. No unchanged Mathlib search was repeated.

The direct-delivery brief and stages/1-dag.md section 2 forbid editing another worker's node. The brief also forbids modifying or bypassing launcher gates. A maintainer must synchronize the existing external node's proof_deps with its proof-step uses. That repair is outside this item's authorized scope. Only this sandbox report was updated; the item, citations and logged searches are retained unchanged.


## Dispatcher retry at 2026-10-21T06:43:57+00:00

Retained the existing item, report, citations and logged search results. The mandatory first dry run, `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`, completed with exit code 1 after server preflight admission. Its sole finding was `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The invocation has exited; nothing was pushed.

I compared the retained item with the current read-only repository: only blueprint, statement, stmt_deps, mathlib_searches, mathlib_match, status and split_report differ. I read the current blueprint's two definition clauses, the chapter and unit records, all six statement-dependency statements, the actual retained search results, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, Algebra.IsSeparable.isAlgebraic and the project's finite-extension equivalence. These continue to support the retained Mathlib leaf. A project-source search found no declaration defining both notions or bearing this item's blueprint tag. No mathematical changes or repeated searches were needed.

I directly opened the external node and confirmed that its fourth step includes this item in uses while proof_deps omits it. The direct-delivery brief and stages/1-dag.md section 2 prohibit changing another worker's node, and the brief prohibits patching or bypassing launcher gates. This tool failure therefore requires a maintainer correction outside the authorized scope. Only this sandbox report was updated; the complete leaf, citations and search log remain retained.


## Dispatcher retry at 2026-10-21T06:46:00.790857+00:00

Retained the item, citations, report and actual search log. The required first dry run (`python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`) exited 1 after server preflight admission with the sole finding: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

I compared the retained item with the current repository, read the chapter and unit records, all six statement dependencies, the current blueprint definition, and the retained search results. I reopened the Mathlib definitions IsSepClosed and IsSepClosure, isSepClosure_iff, the separability-to-algebraicity instance, and the project finite-extension characterization. The retained leaf remains supported; no search repetition or mathematical change is needed. I read delivery-errors B through E and directly confirmed that the external node cites this item in its fourth step but omits it from proof_deps. The sandbox changes only the assigned item. The direct-delivery brief forbids editing another worker's node and forbids modifying or bypassing launcher gates, so the required repair is outside this worker's scope. Only this report was updated; a maintainer must correct the external dependency metadata before delivery can pass.


## Dispatcher retry at 2026-10-21T06:47:20.929307+00:00

Retained the existing item, report, citations and actual search log. The mandatory first dry run (`python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q30 def-kun-separably-closed --no-push`) exited 1 after server preflight admission in slot 4. Its sole finding was: `deps: lem-kun-proper-torsion-cd-bound step 4 uses def-kun-separably-closed, which is not in proof_deps`. The process has exited; nothing was pushed.

Compared the retained item with the current repository, read the chapter/unit records, all six statement dependencies, the current blueprint definition and the retained actual search results. Reopened Mathlib IsSepClosed, IsSepClosure, isSepClosure_iff, Algebra.IsSeparable.isAlgebraic and the project finite-extension characterization. These continue to support the retained Mathlib leaf. No mathematical repair or repeated search was needed. Read delivery-errors B through E; the definition has no proof steps, no new nodes and no proof-step citation obligations.

Directly confirmed the external proper-torsion-bound node lists this item in its fourth step but omits it from proof_deps. Stage 1 section 2 forbids changing another worker's node; the direct-delivery brief also forbids launcher patches and gate bypasses. A maintainer must repair the external dependency metadata. Only this sandbox report was updated; all retained item, citation and search files remain unchanged.


## Successful dispatcher retry at 2026-10-21T06:49:51.733759+00:00

The mandatory first dry run retained all earlier work and exited 0: `OK (not pushed) deliver/Q30/def-kun-separably-closed at 53f23937b38: preflight passed`. This supersedes the historical blocker reports above. The current repository's `lem-kun-proper-torsion-cd-bound` now includes `def-kun-separably-closed` in both step 4's uses and proof_deps; I did not edit it.

I compared the retained item against the current source: only statement, stmt_deps, status, mathlib_searches, mathlib_match, blueprint, and split_report differ. I reread the current blueprint, chapter/unit, all six statement-dependency statements, Mathlib IsSepClosed and IsSepClosure, isSepClosure_iff, the separability-to-algebraicity instance, and the project finite-extension equivalence. Both definition clauses and the constant-polynomial edge case remain correct. The fresh project search found the partial characterizations, but no declaration covering the whole two-clause item. I read and retained the actual logged searches without repeating unchanged questions. B--E still require no mathematical repair: no new nodes, no proof steps, and no hidden long argument. The empty citations list remains appropriate. Only this sandbox report was updated; I will rerun the final dry run on that update and then deliver.
