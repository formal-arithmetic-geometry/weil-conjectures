# Q29: thm-sf-weil-compact-direct-image-right-adjoint

## Files written

Copied the current item unchanged to dag/nodes/sec-six-functors/thm-sf-weil-compact-direct-image-right-adjoint.json. No new nodes; no Mathlib leaves; no proposed changes to the live split.

## Attachments

None. AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek at lean/WeilConjectures/WeilSheaf/VerdierDual.lean:81 has proof `sorry` at line 82. The right-adjoint definition and adjunction below it require HasUpperShriek as a hypothesis and do not prove existence.

## Wanted literature

None.

## Assignment superseded

At the first read, the live item already had status split and reviewed.result pass, dated 2026-10-22, by L, group Q06, reviewer NT-cc-Q06-9ef1bbcb3. Its accepted split has nine steps and the maintainer records a full independent review. The standing stage-1 brief says live split-and-reviewed nodes win and must never be split again. This assignment therefore cannot produce a new split without overriding accepted live work.

## Unfinished work

No replacement split or push attempted. Request the dispatcher retire this stale assignment. The first required dry run exited 1 because report.md was missing; this report repairs that packaging prerequisite so the delivery tool can diagnose the actual current state.

## Review by Q29

I checked the live item's status and review metadata against its actual JSON, rather than relying on a queue entry. I searched the project Lean source for the item tag, HasUpperShriek, and isLeftAdjoint_derivedLowerShriek, then read VerdierDual.lean through the existence theorem and the named upperShriek and adjunction. The theorem at lines 81-82 is explicitly sorried, so an ATTACH answer would be false. The existing live review is by Q06, not by Q29; I have not represented its mathematical review as my own. I copied the item byte for byte and retained all its proof, citations, searches and maintainer fields. No new statement, source, proof step, hypothesis or dependency was introduced, so a new mathematical self-review and new searches would serve no new split. This report records supersession instead of modifying a split that the brief forbids replacing.

The second dry run required citations.json before checking delivery admissibility. I supplied verbatim full statement quotations for the existing split's citations, without changing or claiming authorship of its proof.

## Final dry-run result

The final deliver.py --no-push invocation exited 1 after the server preflight: “the item's node file is unchanged”. Nothing was pushed. Changing the already approved split merely to pass this gate would violate the live-wins rule; the dispatcher must retire this superseded assignment.

## Retry verification, 2026-10-22

The resumed worker first ran the required dry run with the existing item and report retained. It exited 1 after server preflight, again with the sole reason "the item's node file is unchanged"; nothing was pushed. A byte comparison confirms the sandbox item is identical to the current read clone. The live item remains split with reviewed.result=pass, group Q06, reviewer NT-cc-Q06-9ef1bbcb3, dated 2026-10-22. I re-read the standing brief's explicit rule that live split-and-reviewed nodes win and must never be split. I also repeated the project-source search and read VerdierDual.lean:60-98: the existence theorem still has sorry and the named adjunction requires HasUpperShriek, so this is not an ATTACH. There is no authorized node repair that addresses this unchanged-item gate: changing an already accepted split solely for admission would conflict with the live-wins rule. The stale dispatcher assignment needs retirement; all earlier files and mathematical content have been retained.

## Dispatcher retry verification, 2026-10-22 (current attempt)

I retained the earlier report, citations and item unchanged and ran the required `python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py Q29 thm-sf-weil-compact-direct-image-right-adjoint --no-push` once. I polled that same process until it exited with code 1. Server preflight reported exactly one failure: "the item's node file is unchanged". Nothing was pushed.

A fresh byte comparison with the read clone is true. The current live node remains `status: split`, reviewed PASS by L for Q06 on 2026-10-22, reviewer `NT-cc-Q06-9ef1bbcb3`, with nine proof steps. I re-read `coord/brief-stage1.md` under "Isolated new-target run": "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Thus this diagnostic has no permissible sandbox repair: modifying the accepted node solely to manufacture a delivery diff would evade that rule. The dispatcher assignment needs retirement.

I repeated the read-only source search under `lean/WeilConjectures/` for the item id, `HasUpperShriek` and `isLeftAdjoint_derivedLowerShriek`, and read `VerdierDual.lean:58-103`. The existence theorem at lines 81-82 still has `sorry`; the chosen right adjoint and adjunction below it assume `HasUpperShriek`. Hence ATTACH remains invalid. I read GOAL.md and the stage-1 rules and delivery-errors sections B-E; no new mathematical statement, node, search record or proof change is proposed. No repository or launcher file was written, no git command was run, and no compiler or build was invoked.

## Resumed dry-run verification, 2026-10-22

This resumed attempt retained the item, all prior report sections, and citations. The required dry run was invoked once and its single process was polled to completion (exit 1). The server preflight's sole diagnostic was: "the item's node file is unchanged"; it explicitly said nothing was pushed. A subsequent byte comparison still found the sandbox item identical to the live read clone, whose nine-step split remains reviewed PASS for Q06 by NT-cc-Q06-9ef1bbcb3.

I checked GOAL.md, the worker and stage-1 instructions, SETUP.md's three blueprint levels, delivery-errors B–E, the chapter/unit records, and the live-wins instruction in coord/brief-stage1.md. I re-read the native existence theorem in VerdierDual.lean:81–82: its proof remains sorry, so the item cannot be attached. There is no permitted repair for an unchanged delivery of an already accepted split: the standing brief expressly forbids splitting live split-and-reviewed nodes. No item content, citation, recorded Mathlib search, Lean file, repository file or launcher file was changed. The blocker is the stale dispatcher assignment, which needs retirement; no push was attempted after the failed dry run.


## Final dispatcher retry, 2026-10-22

Started with the retained item and report and ran the required dry run once. Polled that same process (session 82133) until it exited 1. Server preflight again reported exactly one reason: "the item's node file is unchanged" and "nothing pushed". A fresh byte comparison with the current read clone is true. The current item remains a nine-step split, reviewed pass by L for Q06, reviewer NT-cc-Q06-9ef1bbcb3, dated 2026-10-22.

Re-read the standing brief, stage-1 document, worker role, GOAL.md, SETUP.md's three blueprint levels, delivery-errors B–E, and the item's chapter and unit records. The standing brief's live-wins instruction remains explicit: "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Searched lean/WeilConjectures for the item id, HasUpperShriek, and isLeftAdjoint_derivedLowerShriek and read VerdierDual.lean:58–104. The existence theorem at lines 81–82 still has sorry; the upperShriek construction and adjunction assume HasUpperShriek, so they cannot support ATTACH. No authorized change can repair this preflight rejection without replacing accepted work. The dispatcher must retire the superseded assignment. Retained all item content, citations, searches and earlier report sections; this report appendix is the only sandbox change. No push, compiler, git command, agent, or repository/launcher write was attempted.


## Current resumed verification, 2026-10-22 05:16 UTC

Retained the prior item, citations and report. Ran the required deliver.py --no-push once and polled its single process (session 26284) to completion: exit 1, sole preflight diagnostic "the item's node file is unchanged", nothing pushed. A fresh byte comparison confirms the sandbox node still equals live, whose split is reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3. Re-read the stage-1 brief, delivery-errors B–E, stage-1 document, GOAL.md, worker role, SETUP.md three levels, chapter and unit records. Repeated the project Lean source search and read VerdierDual.lean:58–105; the existence theorem remains sorry at line 82, while the named adjunction assumes HasUpperShriek, so ATTACH is unsupported. The standing brief says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." No mathematical change is authorized to manufacture a diff for this superseded assignment. Dispatcher retirement is needed. Only this sandbox report appendix was written; no push, compiler, build, git command, agent, repository write, or launcher edit was performed.


## Resumed dispatcher check, 2026-10-22 (session 47937)

Retained the earlier item, report, citations and search records. Ran the required dry run once and polled the same process to its exit: code 1, sole server-preflight failure “the item's node file is unchanged”, nothing pushed. The sandbox node remains byte-identical to the current live node: nine proof steps, status split, reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22.

Rechecked the worker/stage-1 guidance, GOAL.md, SETUP.md’s three levels, the chapter and unit records, and delivery-errors B–E. The standing brief’s live-wins rule still says “Live finished/mathlib/merged/split-and-reviewed nodes win; never split one.” Repeated the project-source search and read VerdierDual.lean:58–103: isLeftAdjoint_derivedLowerShriek still has sorry at line 82, while upperShriek and its adjunction assume HasUpperShriek. Thus no ATTACH is justified. There is no authorized repair to the unchanged-item gate: manufacturing a node change would replace already accepted work. This superseded assignment needs dispatcher retirement. No push was attempted; only this sandbox report appendix was written.

## Resumed dispatcher verification, 2026-10-22 (session 78597)

Retained the existing item, citations and all earlier report sections. Started with the required dry run and polled its single process to completion. It exited 1 with the sole server-preflight failure: "the item's node file is unchanged"; nothing was pushed. A fresh byte comparison confirms the sandbox item equals the current read clone. The live item remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22, with nine proof steps.

Re-read the project goal, worker and stage-1 rules, SETUP.md's three blueprint levels, delivery-errors B–E, and the chapter and unit records. The standing brief explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Thus there is no authorized repair for this preflight diagnostic: changing an accepted split solely to manufacture a diff would violate that rule. The assignment needs dispatcher retirement.

Repeated the read-only project-source search for the item id, HasUpperShriek and isLeftAdjoint_derivedLowerShriek, and read VerdierDual.lean:58–105. The existence theorem still has sorry at lines 81–82; upperShriek and its named adjunction assume HasUpperShriek. No ATTACH is justified. No mathematical content, citation or logged search was changed. Only this sandbox report appendix was written; no push, Lean edit, compiler, build, git command, agent, repository write or launcher edit was performed.


## Required resumed dry run, 2026-10-22 05:22 UTC

Retained the existing item, citations, searches and report. Started with one required deliver.py --no-push invocation and polled its single process (session 25551) until exit 1. Server preflight gave exactly one failure: "the item's node file is unchanged"; nothing was pushed. A fresh byte comparison confirmed that the sandbox node equals the live read clone, which remains split and reviewed PASS for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22, with nine proof steps.

Re-read the worker rules, stage-1 document, GOAL.md, SETUP.md three levels, delivery-errors B–E, chapter/unit records, and the standing brief's live-wins instruction: "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Repeated the project-source search and read VerdierDual.lean:58–105: isLeftAdjoint_derivedLowerShriek still has sorry at line 82; the named upperShriek and adjunction assume HasUpperShriek. ATTACH is therefore unsupported. No authorized repair can produce a delivery difference without replacing accepted work. The dispatcher must retire the superseded assignment. Only this sandbox report appendix was written; no push, repository/launcher write, git command, Lean edit, build, compiler, or agent was attempted.


## Resumed required dry run, 2026-10-22 (session 85800)

Retained the existing item, citations, searches and report. Started with the required deliver.py --no-push invocation and polled the same process to completion. Server preflight rejected it with exactly one reason: "the item's node file is unchanged"; nothing was pushed. A fresh byte comparison confirms the sandbox item equals the current live read clone. The live item remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22.

Rechecked the project goal, worker and stage-1 instructions, SETUP.md, delivery-errors B–E, and chapter/unit records. The standing brief says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Repeated the source search under lean/WeilConjectures and read VerdierDual.lean:58–104: the existence theorem still contains sorry, and upperShriek and its named adjunction assume HasUpperShriek. ATTACH is therefore unsupported. No authorized repair can manufacture a delivery difference for an accepted split; the stale dispatcher assignment needs retirement. Only this sandbox report appendix was written. No push, repository/launcher write, git command, Lean edit, compiler, build, or agent was attempted.


## Resumed verification, 2026-10-22 (session 69810)

Retained all earlier item content, citations and report sections. Started with the required dry run and polled its single process until exit 1. The sole server-preflight diagnostic was "the item's node file is unchanged"; nothing was pushed. A byte comparison confirms that the sandbox node is identical to the current read clone: status split, nine proof steps, reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22.

Read the worker and stage-1 instructions, GOAL.md, SETUP.md's three blueprint levels, delivery-errors B–E, and the chapter/unit records. The standing brief explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." This superseded assignment therefore has no permitted node change that repairs the unchanged-item gate. Repeated the project-source search for the item id, HasUpperShriek and isLeftAdjoint_derivedLowerShriek and read VerdierDual.lean:55–110. The existence theorem still has sorry at lines 81–82; upperShriek and its adjunction assume HasUpperShriek, so ATTACH remains unsupported. Dispatcher retirement is needed. Only this sandbox report appendix was written; no push, repository or launcher write, git command, Lean edit, compiler, build, or agent was attempted.

## Resumed dry-run result, 2026-10-22 (session 73313)

Retained all saved files and ran the required dry run once, polling the same process until exit 1. Server preflight reported its sole failure: "the item's node file is unchanged"; nothing was pushed. The sandbox item is byte-identical to live, which remains split and reviewed PASS for Q06 by NT-cc-Q06-9ef1bbcb3. The standing brief at coord/brief-stage1.md:105 says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." No permitted mathematical repair addresses this gate for a superseded assignment. Read GOAL.md, worker/stage-1 rules, delivery-errors B–E, SETUP.md's three levels, and chapter/unit records. Rechecked project source: VerdierDual.lean:81–82 still has sorry, and the right-adjoint construction assumes HasUpperShriek, so ATTACH is unsupported. Dispatcher retirement is required. Only this report appendix was written; no push, repository/launcher edit, git command, compiler, build, or agent was run.


## Resumed dry-run verification, 2026-10-22 (session 11870)

Retained the item, citations, recorded searches and prior report. The required dry run exited 1 after polling its sole process to completion: preflight reported exactly one reason, "the item's node file is unchanged", and nothing was pushed. A fresh byte comparison confirms the sandbox item equals live. Live remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3. The standing brief explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Therefore no permitted node repair addresses this gate; the dispatcher must retire this stale assignment.

Read the required worker/stage-1 rules, GOAL.md, SETUP.md's three levels, delivery-errors B–E and the chapter/unit records. Repeated the project-source search and read VerdierDual.lean:55–105: the existence theorem at lines 81–82 still contains sorry, and the chosen upperShriek and adjunction assume HasUpperShriek, so ATTACH is unsupported. This report appendix is the only sandbox change. No push, repository/launcher edit, git command, Lean edit, compiler, build or agent was attempted.

## Resumed required dry run, 2026-10-22 (session 16353)

Retained all prior files and ran the required dry run once, polling that same process until exit 1. Server preflight reported exactly one failure: "the item's node file is unchanged"; nothing was pushed. A fresh byte comparison confirms the sandbox item equals the current live node, which remains split and reviewed PASS for Q06 by NT-cc-Q06-9ef1bbcb3. The standing brief explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Thus the stale assignment has no permitted node repair and needs dispatcher retirement.

Read the required worker and stage-1 rules, GOAL.md, SETUP.md's three levels, delivery-errors B–E and chapter/unit records. Repeated the project-source search and read VerdierDual.lean:55–103: the existence theorem still has sorry at lines 81–82, while the right-adjoint construction and adjunction assume HasUpperShriek. ATTACH is unsupported. Only this report appendix was written; the item, citations and searches were retained unchanged. No push, repository/launcher write, git command, Lean edit, compiler, build or agent was attempted.

## Resumed required dry run, 2026-10-22 (session 58447)

Retained all saved item content, citations, searches and report sections. Ran the required dry run once and polled that same process until exit 1. Server preflight reported exactly one failure: "the item's node file is unchanged"; nothing was pushed. A fresh byte comparison confirms that the sandbox item equals the current read clone. The live item remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22.

Read GOAL.md, worker and stage-1 instructions, SETUP.md's three blueprint levels, delivery-errors B–E, and the chapter/unit records. The standing brief explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Repeated the project-source search for the item id, HasUpperShriek and isLeftAdjoint_derivedLowerShriek and read VerdierDual.lean:55–110: the existence theorem still has sorry at lines 81–82, while the right-adjoint construction and adjunction assume HasUpperShriek. ATTACH remains unsupported. No permitted node repair resolves the unchanged-item gate for this accepted split; the dispatcher must retire this stale assignment. Only this sandbox report appendix was written. No push, repository/launcher write, git command, Lean edit, compiler, build or agent was attempted.


## Required resumed dry run, 2026-10-22 05:44 UTC (session 86919)

Retained the item, citations, recorded searches and all earlier report sections. Ran the required deliver.py --no-push once and polled that process until exit 1. Server preflight reported exactly one failure: "the item's node file is unchanged"; nothing was pushed. A fresh byte comparison confirms the sandbox item equals the current read clone. The live item remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3.

Read the worker and stage-1 instructions, GOAL.md, SETUP.md's three blueprint levels, delivery-errors B–E, and the chapter/unit records. The standing brief explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Repeated the source search under lean/WeilConjectures and read VerdierDual.lean:55–108: isLeftAdjoint_derivedLowerShriek still contains sorry at line 82; upperShriek and the named adjunction assume HasUpperShriek. ATTACH is unsupported. No permitted node repair resolves the unchanged-item gate for an accepted live split. This stale assignment needs dispatcher retirement. Only this sandbox report appendix was written; no push, repository/launcher write, git command, Lean edit, compiler, build or agent was attempted.

## Resumed dry run, 2026-10-22 (session 46596)

Retained all saved files. The required single dry run exited 1 with the sole server-preflight diagnostic "the item's node file is unchanged"; nothing was pushed. The sandbox item is byte-identical to the current live node, which is split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3. The standing brief at coord/brief-stage1.md:105 explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." There is no permitted node repair for this superseded assignment; dispatcher retirement is required. Rechecked the worker/stage-1 rules, delivery-errors B–E, SETUP.md's three levels, GOAL.md, chapter/unit records, and project source. VerdierDual.lean:81–82 still contains sorry; the right adjoint and adjunction below it assume HasUpperShriek, so ATTACH is unsupported. Only this report appendix was changed; no push, repository/launcher write, git command, Lean edit, compiler, build or agent was attempted.


## Resumed required dry run, 2026-10-22 05:48 UTC (session 34777)

Retained all existing item content, citations, recorded searches and report sections. Started with the required deliver.py --no-push invocation and polled its single process to completion (exit 1). Server preflight reported two reasons: (1) "the item's node file is unchanged"; (2) "re-split (the human, 2026-10-21): the item's proof in words is still 9479 characters; split further until it is at most 3000 characters (each non-elementary argument a new statement-only node the step cites)". Nothing was pushed.

A fresh byte comparison confirms the sandbox node equals the current read clone. The live item remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3. The standing brief at coord/brief-stage1.md:105 explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Both preflight diagnostics require changing this already accepted split; no such repair is permitted for this stale assignment. Dispatcher retirement or an explicit assignment reopening the accepted split is required.

Read the worker and stage-1 rules, GOAL.md, SETUP.md's three levels, delivery-errors B–E, and chapter/unit records. Repeated the project-source search for the item id, HasUpperShriek and isLeftAdjoint_derivedLowerShriek and read VerdierDual.lean:55–110. The existence theorem at lines 81–82 remains sorry; upperShriek and the named adjunction assume HasUpperShriek, so ATTACH is unsupported. Only this report appendix was written. No node content, citations or search records were changed, and no push, repository/launcher write, git command, Lean edit, compiler, build or agent was attempted.


## Resumed required dry run, 2026-10-22 (session 48808)

Retained the prior item, citations, search records and report. Ran the required deliver.py --no-push once and polled that same process to completion (exit 1). Server preflight rejected the delivery for two reasons: "the item's node file is unchanged" and "the item's proof in words is still 9479 characters; split further until it is at most 3000 characters". Nothing was pushed. The sandbox item remains byte-identical to live, which remains split and reviewed PASS for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22.

Re-read GOAL.md, the worker and stage-1 instructions, SETUP.md's three blueprint levels, delivery-errors B–E, and the chapter/unit records. The standing brief explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Thus neither diagnostic has an authorized sandbox repair: resplitting the accepted live item to meet the length gate would violate that instruction. The stale assignment needs dispatcher retirement or an explicit authorized reopening; the launcher gate was not patched or bypassed.

Repeated the read-only source search under lean/WeilConjectures and read VerdierDual.lean:58–105. The existence theorem isLeftAdjoint_derivedLowerShriek still has sorry at line 82; upperShriek and its adjunction assume HasUpperShriek. ATTACH would therefore be unsupported. No mathematical content, citation, or search record changed. Only this sandbox report appendix was written; no push, repository/launcher write, git command, Lean edit, compiler, build, or agent was attempted.


## Resumed required dry run, 2026-10-22 (session 85902)

Retained the saved item, citations, recorded searches and all earlier report sections. Ran the required deliver.py --no-push once and polled its single process to completion, exit 1. Server preflight rejected the unchanged item and its 9479-character proof, requiring at most 3000 characters. Nothing was pushed. A fresh byte comparison confirms that the sandbox item equals the current live read clone. Live remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22.

Read GOAL.md, the worker and stage-1 rules, SETUP.md's three levels, delivery-errors B–E, and the chapter/unit records. coord/brief-stage1.md explicitly says: "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Resplitting this accepted live item to repair the length gate is therefore prohibited; this superseded assignment needs dispatcher retirement or an explicit authorized reopening. No launcher gate was patched or bypassed.

Repeated the project-source search for the item tag, HasUpperShriek and isLeftAdjoint_derivedLowerShriek and read VerdierDual.lean:55–108. The existence theorem at lines 81–82 still contains sorry. upperShriek and its named adjunction assume HasUpperShriek, so ATTACH is unsupported. Only this sandbox report appendix was written; no node content, citations or search records changed, and no push, repository/launcher write, git command, Lean edit, compiler, build or agent was attempted.


## Resumed required dry run, 2026-10-22 06:17 UTC

Retained all saved files and ran the required deliver.py --no-push once, polling the same process (session 12803) until exit 1. Server preflight rejected the unchanged item and its 9479-character proof, requiring at most 3000 characters. Nothing was pushed. A fresh byte comparison confirms that the saved item equals the current live node. Live remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22.

The standing brief explicitly says: "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Both diagnostics require modifying an already accepted live split, so this superseded assignment has no permitted node repair. The dispatcher must retire the stale assignment or explicitly reopen the accepted split. No gate was patched or bypassed.

Rechecked GOAL.md, the worker and stage-1 rules, SETUP.md's three blueprint levels, delivery-errors B–E, and the chapter/unit records. The read-only project-source search and VerdierDual.lean:55–105 show that isLeftAdjoint_derivedLowerShriek still contains sorry at line 82; upperShriek and its adjunction assume HasUpperShriek. ATTACH remains unsupported. Only this report appendix was written; no item, citation, search record, repository or launcher file changed. No push, git command, Lean edit, compiler, build or agent was attempted.


## Resumed required dry run, 2026-10-22 (session 50913)

Retained all saved files and ran the required deliver.py --no-push once, polling the same process to its exit (1). Server preflight rejected two things: "the item's node file is unchanged" and its 9479-character proof, requiring a further split to at most 3000 characters. Nothing was pushed. A fresh byte comparison confirms the sandbox item equals the live node. Live remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3 on 2026-10-22.

The standing brief explicitly says "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Consequently this superseded assignment has no permitted repair to either gate: it requires dispatcher retirement or explicit reopening of the accepted live split. No gate was patched or bypassed. Rechecked GOAL.md, the worker and stage-1 rules, SETUP.md's three blueprint levels, delivery-errors B–E, and the chapter/unit records. Repeated the source search in lean/WeilConjectures and read VerdierDual.lean:55–108: isLeftAdjoint_derivedLowerShriek still contains sorry at lines 81–82; upperShriek and its adjunction assume HasUpperShriek. ATTACH is unsupported. Only this report appendix was written; item content, citations and searches were retained unchanged. No push, repository/launcher write, git command, Lean edit, compiler, build or agent was attempted.


## Resumed required dry run, 2026-10-22 (session 5950)

Retained all saved files and ran the required deliver.py --no-push once, polling the same process until exit 1. Server preflight rejected the unchanged item and its 9479-character proof, requiring a further split to at most 3000 characters. Nothing was pushed. A fresh byte comparison confirms the sandbox item equals live, which remains split and reviewed pass for Q06 by NT-cc-Q06-9ef1bbcb3.

Read GOAL.md, worker/stage-1 rules, SETUP.md three levels, delivery-errors B–E, and chapter/unit records. coord/brief-stage1.md:105 explicitly says: "Live finished/mathlib/merged/split-and-reviewed nodes win; never split one." Resplitting the accepted live item is forbidden under that instruction, so the dispatcher must retire this superseded assignment or explicitly reopen it. No launcher gate was patched or bypassed. Repeated the project-source search and read lean/WeilConjectures/WeilSheaf/VerdierDual.lean:55–105: the existence theorem at lines 81–82 still contains sorry; upperShriek and its adjunction assume HasUpperShriek, so ATTACH is unsupported. Only this report appendix changed; item content, citations and recorded searches were retained. No push, repository/launcher write, git command, Lean edit, compiler, build or agent was attempted.


## Reopened repair, 2026-10-22: supersedes the earlier blocked dispositions

The current coord/repair-notes/thm-sf-weil-compact-direct-image-right-adjoint.json has state released, stage 1, keep_plan true and date 2026-10-22. It explicitly reopens the earlier passing Q06 split, requires at least three new statement-only nodes and an assembly of at most 3000 characters. The standing brief now explicitly makes that record an exception to live-wins. The earlier report paragraphs remain history; their conclusion that resplitting is forbidden no longer applies. No dispatcher retirement is needed for this repair. I retained the item statement, stmt_deps, blueprint anchor, source and all maintainer fields, and changed only the authorized split fields. The original nine steps are preserved verbatim below, with their ownership mapped to the new obligations. This is an authorized spreading of the existing work, not a new proof route.

The first resumed dry run was started before any repair. Its tool process became unavailable during the provider interruptions; a process-list check established that no deliver.py process for this item remained before another invocation. The next invocation reached server preflight, but its final tool-session result was likewise unavailable after interruption. I did not infer success from either run. The new dry run below validates the actual repaired files; only one delivery invocation is active at a time.

## Files written for the reopened repair

- dag/nodes/sec-six-functors/thm-sf-weil-compact-direct-image-right-adjoint.json: unchanged statement and stmt_deps, four-step assembly, 2403 characters of proof text.
- dag/nodes/sec-six-functors/lem-sf-native-weil-derived-induction-comparison.json: statement, unsplit, no Mathlib match. Grothendieck/K-injective setup, actual derived forget comparison and free-induction comparison, formerly steps 2-4.
- dag/nodes/sec-six-functors/lem-sf-native-weil-localizing-brown-adjoints.json: statement, unsplit, no Mathlib match. Inverse-image description of the Weil hull and the two ordinary localizing Brown adjoints, formerly steps 5-6.
- dag/nodes/sec-six-functors/lem-sf-native-geometric-brown-constructible-comparison.json: statement, unsplit, no Mathlib match. Realized constructible adjunction, normalized counit and comparison with any geometric localizing adjoint, formerly steps 1 and 7.

All three new nodes have empty proof and proof_deps, null proof_origin and mathlib_match, complete self-contained statements, explicit sources and blueprint origins. They have comparable sizes and separate outputs: comparisons of left functors; existence on localizing hulls; comparison and constructibility of the geometric right functor. None states the required native bounded-constructible Weil right adjoint. The item still performs its essential five-adjunction Hom calculation and restriction itself.

## Attachments for the reopened repair

None. I read VerdierDual.lean:55-105: AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek at lines 81-82 still has sorry. The right-adjoint definition assumes HasUpperShriek. Operations.lean:91-109 proves a derivedLowerStar/forget comparison, but it covers neither compact-support free induction nor the Brown/constructible assertions, so it is not an attachment of any new node. BrownRepresentabilityRightAdjoint.lean:47 requires compact generation, whereas the retained route uses a set-generated Grothendieck-derived solution set and does not assert compactness. Its theorem is not an exact attachment of the new Brown node.

## Wanted literature for the reopened repair

None. This repair follows the existing agent-written ordinary-derived expansion, with the exact expansion retained below, of the final sentence in main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md. I read that file, the historical thm-coef-qbar-verdier.md, and the open/proper bullets and last paragraph of main-20261015/blueprint/sec-six-functors-basics/sk-prop-int-brown/sk-prop-int-brown-construction.proof.md. These paragraphs supply the intended equivariance/adjunction and localizing route; they do not themselves prove the native ordinary-derived comparisons. The new nodes clearly label these as agent-formulated obligations. No prohibited SGA route or source is introduced. The chapter and unit files were read without changing them.

## Existing-node and blueprint searches

Before writing the new nodes I searched all dag/nodes for induction comparison, free induction, Brown adjoint, localizing Weil, constructible counit and the explicit expressions U_YF_W, I_YFA, G_cM and Loc(I_T. I read each old dependency's statement, and also the likely duplicates named below. I ran tools/blueprint_refs.py search for Weil, induction comparison, localizing, constructible adjoint, free induction, solution set, constructible exceptional, induction, and right adjoint, across all blueprint nodes. Relevant matches concern stage coefficients, separated condensed-module categories or general categorical inputs, rather than any one of the three complete new statements. I also searched lean/WeilConjectures by the item id, HasUpperShriek, isLeftAdjoint_derivedLowerShriek, Brown, free Weil and induction. The existing exact generic facts are reused. All three new ids were checked absent from the whole DAG before writing them.

The ancestor command returns None: the maintainer-created item has created.item=null. Accordingly new blueprint.from.node=null and via=[the item], exactly as for the already accepted Q06 children; from.place records the supplied lem-a1-local-boundary-duality anchor and quotes the actual current exceptional-adjunction sentence, followed by the exact old step range served. This retains the existing anchor rather than manufacturing a different ancestor. same_as is [] for each node after the searches.

## Not duplicates

lem-sf-native-weil-derived-induction-comparison vs lem-sf-fixed-pair-derived-forget-comparison: the existing node gives the generic derived forget comparison for one left exact lift; the new node identifies the actual composite Rp_*D(j_!) and also constructs and normalizes its comparison with free induction on the native localizing hull.
lem-sf-native-weil-derived-induction-comparison vs lem-sf-free-derived-weil-resolution: the latter gives I, U and the cyclic resolution for one heart, not the compact-support functor, the normalized beta or kappa.
lem-sf-native-weil-derived-induction-comparison vs lem-weil-pbc-kinjective-exact-square-comparison: the latter supplies an abstract normalized comparison under K-injective hypotheses; the new statement discharges the native sheaf square, builds the compact-support composite and includes induction with all integer Frobenius powers.
lem-sf-native-weil-derived-induction-comparison vs lem-weil-pbc-right-adjoint-preserves-kinjective: the latter is only the general preservation criterion used in the native setup, with none of the new comparisons.
lem-sf-native-weil-localizing-brown-adjoints vs det-sf-existence-brown: the existing result concerns separated schemes and condensed stage coefficients and assumes compact generation; the new assertion uses the actual locally finite B_T coefficients and native Weil heart, non-absolutely-separated schemes, cyclic generation and set-generated solution sets, with no compact-generator assertion.
lem-sf-native-weil-localizing-brown-adjoints vs det-prop-int-brown-adjoint: the existing statement is integral, separated, and non-equivariant; the new statement concerns locally finite algebraically closed field coefficients and ordinary native Weil hulls as well as the geometric hull.
lem-sf-native-weil-localizing-brown-adjoints vs lem-sfb-set-generated-derived-solution-set: the generic existing node supplies only weakly universal element families for an already specified Grothendieck-derived hull; the new obligation establishes the native Weil hull and functor hypotheses and the assembled two adjoints.
lem-sf-native-geometric-brown-constructible-comparison vs lem-sf-constructible-exceptional-adjunction-coefficients: the latter is the coefficient-stage adjunction, not its realization on B_T-modules or its identification with a right adjoint on the native localizing hull.
lem-sf-native-geometric-brown-constructible-comparison vs lem-sf-locally-finite-adic-compact-support-realization: the existing node compares only the left functor; the new node specifies the transported right functor, counit, and comparison to a localizing right adjoint.
lem-sf-native-geometric-brown-constructible-comparison vs det-sp-comparison-brown-unique: the existing result is smooth-purity comparison and presupposes constructible restriction; the new node proves the restriction for arbitrary separated finite-type f using the orthogonality comparison cone.
lem-sf-native-geometric-brown-constructible-comparison vs det-sf-determination-localizing: the existing theorem tests a natural transformation between two exact coproduct-preserving functors; the new comparison has a right adjoint not known to preserve coproducts and uses right orthogonality of its cone instead.
lem-sf-native-geometric-brown-constructible-comparison vs lem-sf-adic-qbar-constructible-realization: the existing node is an equivalence for absolutely separated schemes and a different coefficient presentation, not the adjoint/counit/orthogonality assertion needed here; the precise locally-finite realization is reused instead.

lem-sf-native-weil-derived-induction-comparison vs def-weil-pbc-derived-tower-models: defines towerwise derived model data and asserts no existence or native compact-support/Frobenius comparison; the new theorem supplies the actual native beta and free-induction kappa.
lem-sf-native-weil-derived-induction-comparison vs lem-weil-pbc-exact-square-derived-counit: compares counits for an already supplied normalized beta and exact adjunction squares; the new theorem establishes beta for native compact support and proves the free-induction map invertible on its hull.
lem-sf-native-weil-derived-induction-comparison vs lem-weil-pbc-flat-restriction-derived-mate: assumes a flat ringed diagram, supplied restriction comparison and normalized derived adjunctions to prove a mate invertible; the new statement is a native Frobenius/free-induction comparison with different data and domains.
lem-sf-native-weil-derived-induction-comparison vs lem-weil-pbc-kinjective-total-derived: gives existence and evaluation of a generic total right derived functor, not the native Weil square, Frobenius exchanges or induction comparison.
lem-sf-native-weil-derived-induction-comparison vs lem-sfb-kinjective-direct-image-open-word-model: concerns condensed coefficient direct-image/open-restriction words under invertible coefficient maps, with no native Weil forgetting or free induction; the new theorem includes extension by zero and integer-orbit induction for locally finite coefficients.
lem-sf-native-weil-derived-induction-comparison vs lem-sf-kinjective-replacement-triangulated: gives the triangulated K-injective replacement equivalence for one abelian category, not an identification of two actual native derived operations or their free-induction maps.
lem-sf-native-weil-derived-induction-comparison vs def-sf-normalized-derived-comparison-identifications: defines localization identifications after beta is supplied; the new statement constructs and normalizes beta for native compact support and includes invertibility of kappa.
lem-sf-native-weil-derived-induction-comparison vs lem-asd-clopen-geometric-sections-derived-evaluation: evaluates compact support for finitely many clopen geometric points with constant ring coefficients; the new theorem is the general native locally-finite Weil/free-induction comparison, without any clopen or zero-dimensional hypothesis.
lem-sf-native-weil-derived-induction-comparison vs lem-sf-direct-image-scalar-restriction-cocycle: proves a cocycle for restriction along finite constant coefficient rings, not forgetting a Weil action or induction over integer Frobenius translates.
lem-sf-native-weil-derived-induction-comparison vs lem-sf-exact-localization-derived-triangle: constructs a triangle from exact localization data and an invertible counit; the new theorem supplies beta and kappa for the actual native compact-support functors and claims no such localization triangle.
lem-sf-native-weil-derived-induction-comparison vs lem-sf-kinjective-derived-map-computation: computes generic derived morphisms after choosing resolutions; the new theorem establishes a native comparison of functors and its specific free-induction summand formula.

## Mathlib searches read

The required msearch.py commands were run for each new id's statement in mind: LeanFinder, Loogle, grep and LeanSearch, plus a second semantic phrasing. Exact query text and full printed results are retained in each new node's mathlib_searches and in the sandbox .search-results.json files. searches.jsonl is the command's unmodified log. Early Loogle patterns used unknown identifiers (rightDerivedFunctor and Triangulated); those actual diagnostics are preserved, and I reran with IsRightDerivedFunctor and Pretriangulated respectively. Neither rerun states a new obligation. The broad Brown grep returned author names, so a focused CategoryTheory grep was run and its five solution-set-theorem hits were read. The general adjoint functor theorem there assumes all limits and preservation of limits, which the new triangulated hull assertion does not assume.

For the first node I read Mathlib/Algebra/Category/ModuleCat/Presheaf/Pushforward.lean:103 pushforwardCompToPresheaf: it forgets an underived presheaf module action, not a derived Weil action. Sheaf/Free.lean:213 map_ιFree_mapFreeIso_inv (deprecated alias map_ιFree_mapFree_hom at 218) concerns copowers of a sheaf unit, not free induction for an automorphism. Functor/Derived/Adjunction.lean:144 Adjunction.derived assumes derived pairs and absolute composition conditions, and supplies no native compact-support or integer-orbit comparison. For the third node I read Adjunction/Restrict.lean:42 restrictFullyFaithful: it assumes both functors already restrict and provides none of the constructible realization or right-adjoint preservation. Generic adjunction and triangulation results cannot be a one-line specialization of any full new node. All three therefore remain unsplit, with zero Mathlib leaves.

## Review by Q29

I re-read the current repair order and its keep_plan requirement against both live and sandbox JSON. The item statement and stmt_deps agree exactly, including the finite field, ell invertibility, relative separatedness of f, qcqs Y, finite-type hypotheses on X and Y, native locally finite coefficients and the actual chosen compactification. In particular I did not add absolute separatedness, change finite-Tor coefficient stages into the native category by definition, identify derived Weil hearts with fixed pairs of a derived category, or assume derived forgetting faithful. The leaf existence theorem in Lean is still sorry, so this remains a stage-1 split rather than an attachment.

For the first new statement I read the final exceptional-adjunction sentence, the native framework statement and the generic exact-square/K-injective statements. In Stacks derived.tex I read lemma-adjoint-preserve-K-injectives (08BJ), lemma-K-injective-defined (070Y) and lemma-right-derived-exact-functor (015F), and injectives.tex theorem-K-injective-embedding-grothendieck (079P). The internal B_T-module description is equivalent to ordinary sheaves of B_T-modules by restricting the action along underline Omega to B_T and reversing with the same sectionwise multiplication. Thus the Grothendieck ringed-site node applies on the chosen small site. Exact free I from the existing free-resolution node makes U preserve K-injectives; exact Frobenius equivalences preserve them by the same criterion. This verifies the hypotheses needed for the exact-square comparison. The native lift acts on an arrow by p_*u, so the sheaf square is a square of functors, not just an agreement of objects. Its normalized derived comparison composes with termwise open extension to give beta. The zero summand of U(kappa) is F(eta), all other summands are Frobenius translates, including negative n by the chosen coherent inverse. Their sum is the canonical coproduct comparison on L_X. This entire nontrivial argument is now owned by the first new node, rather than concealed in an assembly step.

For the second new statement I read the Brown construction source and the exact statements of free-derived-weil-resolution, locally-finite realization/sums, set-generated-derived-solution-set, cohomological-solution-set-representability, countable-coproducts-idempotent-complete and right-adjoint-from-objectwise-representability. Exactness and coproduct preservation of I imply I(L_T) is in Loc(I S_T). Exactness and coproduct preservation of U, with UI=the sum of integer translates, give the opposite underlying inclusion, since Frobenius preserves constructibility. The cyclic triangle proves the converse for every K whose underlying object is in L_T. These are three distinct inclusions, not an assumption of equivalence between derived fixed-pair categories. Beta identifies the coproduct comparison of F_W with that of F, and conservativity reflects its invertibility; it also proves image containment. For each of the two left functors, the Hom functor is cohomological by exactness and converts sums to products. The source is the actual hull of a set in the Grothendieck derived category established above; this is exactly the solution-set node's domain. Countable coproducts imply split idempotents, and the representability and objectwise assembly nodes then apply. Hom, generating-set and coproduct universes are kept the same. Nothing asserts a right adjoint outside those hulls. The statement records these intermediate obligations so the next worker can recover every old step 5-6 argument.

For the third new statement I read both realization statements and the coefficient adjunction statement. The first gives an equivalence on derived morphisms and essential smallness, the second the actual left comparison with its direction J_Y F_stage to F J_X, and the coefficient theorem gives the exceptional adjunction with no absolute separatedness. I wrote the counit using alpha inverse, then realized stage counit, then the equivalence counit, in that order; every source and target matches. Transposing gives t. Applying Hom(A[n],-) to t is invertible for every constructible A and shift n by the two adjunctions. For its cone Q, the objects B right-orthogonal to Q in all shifts are closed under triangles by their long exact sequences and under arbitrary coproducts because Hom out of a coproduct is a product. Thus they contain all L_X; taking B=Q forces its identity to vanish, hence Q=0. This proves preservation by G rather than assuming it when restricting. This argument is now the third new node; it is not elementary at the parent level.

I checked every assembly citation against its statement. Step 1 cites the native definition for its actual coefficient categories and operations; the first new node explicitly supplies beta, kappa and their domains; the second explicitly supplies both hull identifications, adjunctions and containments. Step 2 cites the third new node for precisely G_c, t and G(C_Y) subset C_X, and for F's constructible adjunction. Step 3 cites the free-resolution statement for the exact derived I adjunction U, the first new node for kappa, the second for both ambient adjunctions and the domains of the represented objects, and the native definition for the bounded-constructible criterion. The five displayed Hom bijections use exactly those adjunctions, in their given directions. Evaluation on the two identities proves the elementary representing-object identification and its naturality. Step 4 cites the native definition for fullness and equality of the left functor with the chosen native derivedLowerShriek. Containment of the left and right functors was proved in steps 2-3, so restricting the existing Hom bijection is elementary. citations.json gives verbatim statements for every uses entry, without borrowing from a cited proof. No assembly step exceeds 2000 characters; total proof text is 2403 characters.

Small cases checked: X empty or a zero complex gives the zero functor and zero comparisons; an empty coproduct is preserved; for f=id and the identity compactification, beta and kappa reduce to identity comparisons, and both Brown and constructible adjoints reduce to identity. With P=id, free induction is the bilateral sum and the cyclic triangle still generates arbitrary representations. Over a finite-field point, a nontrivial Jordan Frobenius action stays in D(W), so the argument does not collapse its Ext classes by treating derived forgetting as faithful. Negative Frobenius powers are included explicitly, and the cone-orthogonality test uses all integer shifts. Non-absolutely-separated finite-type schemes are allowed throughout: the reused locally-finite realization/sums and coefficient adjunction statements explicitly allow them; none of the separated-only candidates in the duplicate list is applied. For unbounded objects Brown is only used on the specified hulls; boundedness is recovered at the final constructible restriction.

Corrections in this repair: replaced the obsolete live-wins blocker using the released repair record; split the 9479-character proof into three comparable statement-only obligations and a 2403-character assembly; moved the old nontrivial cone comparison out of its elementary parent step; preserved the five Hom bijections and actual-functor restriction; repaired two invalid Loogle patterns and narrowed the noisy Brown grep; regenerated all citations from current node statements. All older proof arguments are retained below. No Lean file, repository/launcher file, compiler/build invocation, git command or agent was used.

## Retained proof arguments and assignment to new nodes

### Original step 1: now owned by lem-sf-native-geometric-brown-constructible-comparison

Put $X=X_0\times_{k_0}k$ and $Y=Y_0\times_{k_0}k$. The quasi-compact locally finite-type hypotheses say that $X_0,Y_0,f_0$ are of finite type. Use the native module categories $\mathcal A_T$, Weil hearts $\mathcal W_T$, and the actual chosen compactification $f_0=p_0j_0$ of [def-sf-native-weil-derived-framework]. Use the current native constructibility convention: locally on $T$, a finite locally closed constructible stratification with a pro-etale covering on each stratum and a finite free model $B_U^{\oplus r_U}$ on each covering member $U$; $r_U$ may depend on $U$. Put $\mathcal C_T=D^b_{\mathrm{cons}}(\mathcal A_T)$ with this convention, and $\mathcal L_T=\operatorname{Loc}(\mathcal C_T)$ on the geometric fibres. The actual geometric left functor is $F=Rp_*D(j_!)$. The realization $J_T$ is an equivalence by [lem-sf-locally-finite-adic-constructible-realization]; [lem-sf-locally-finite-adic-compact-support-realization] identifies $FJ_X$ with $J_YF^{\mathrm{stage}}$. Thus [lem-sf-constructible-exceptional-adjunction-coefficients] gives a constructible adjoint $G_c=J_XG^{\mathrm{stage}}J_Y^{-1}$: its natural Hom bijection is obtained by applying $J_Y^{-1}$, the cited stage adjunction, and $J_X$. Its counit is the realized stage counit composed with the inverse left comparison. The cited coefficient theorem applies at $\Omega$ with its finite-Tor domain; that domain is exactly the source of $J_T$. It permits these schemes without absolute separatedness.

Cited statements: def-sf-native-weil-derived-framework, lem-sf-locally-finite-adic-constructible-realization, lem-sf-locally-finite-adic-compact-support-realization, lem-sf-constructible-exceptional-adjunction-coefficients.

### Original step 2: now owned by lem-sf-native-weil-derived-induction-comparison

The category $\mathcal A_T$ is Grothendieck: its internal $B_T$-modules in $\underline\Omega$-module sheaves are ordinary $B_T$-module sheaves: restrict a $B_T$-action along $\underline\Omega\to B_T$ for one direction; the internal action in the other direction is the same sectionwise multiplication, and both composites recover the original action, so apply [lem-pur-ringed-site-grothendieck-abelian] on the chosen small site. Apply [lem-sf-free-derived-weil-resolution] to the exact Frobenius autoequivalence $P_T$ to obtain a Grothendieck Weil heart and exact derived functors $I_T\dashv U_T$, with $U_T$ conservative and coproduct preserving. Pullback by a scheme isomorphism preserves the local finite-free models and stratifications, so $P_T$ preserves $\mathcal C_T$ and $\mathcal L_T$. Exactness of $I_T$ and [lem-weil-pbc-right-adjoint-preserves-kinjective] show that $U_T$ preserves K-injectives. The required K-injective resolutions exist by [lem-weil-pbc-kinjective-functorial-existence].

Cited statements: def-sf-native-weil-derived-framework, lem-pur-ringed-site-grothendieck-abelian, lem-sf-free-derived-weil-resolution, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-functorial-existence.

### Original step 3: now owned by lem-sf-native-weil-derived-induction-comparison

Let $F_W=Rp_*^{\mathcal W}D(j_!^{\mathcal W})$ on $D(\mathcal W_X)$, exactly the native left functor. At the sheaf level $U_Yp_*^{\mathcal W}=p_*U_Z$, on arrows as well as objects; indeed the current native lift sends $(M,\phi)$ to $(p_*M,p_*(\phi)\circ c_M)$ and an arrow $u$ to $p_*u$, so forgetting recovers exactly ordinary module pushforward along its displayed coefficient map. Apply [lem-weil-pbc-kinjective-exact-square-comparison] with these two forgetful functors and direct images. Step 2 supplies its K-injective hypothesis. The resulting natural comparison is $U_YRp_*^{\mathcal W}\cong Rp_*U_Z$, normalized by identical evaluation on a K-injective Weil complex. Also $U_Zj_!^{\mathcal W}=j_!U_X$ termwise. Composing gives
$$U_YF_W\cong FU_X$$
on the entire ordinary derived categories, including derived morphisms. Both $F_W$ and $F$ are exact: use [lem-sf-exact-functor-derived-triangulated] for the exact open extensions and [lem-pc-right-derived-functor-triangulated] for the additive direct images, with step 2 providing resolutions. This proves the actual left-functor comparison instead of assuming a comparison after equivariant localization.

Cited statements: def-sf-native-weil-derived-framework, lem-weil-pbc-kinjective-exact-square-comparison, lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated.

### Original step 4: now owned by lem-sf-native-weil-derived-induction-comparison

By [lem-sf-locally-finite-adic-compact-support-sums], $F:\mathcal L_X\to\mathcal L_Y$ preserves coproducts. Form the natural map
$$\kappa_A:I_YFA\longrightarrow F_WI_XA$$
as the transpose under $I_Y\dashv U_Y$ of $FA\xrightarrow{F\eta_A}FU_XI_XA\cong U_YF_WI_XA$. Under $U_Y$, on the summand $P_Y^nFA$ it is the isomorphism $P_Y^nFA\to F(P_X^nA)$ followed by $F$ of that summand inclusion. Indeed the zero summand is $F\eta_A$, while the other summands are its translates by the structure isomorphism of the target Weil object. The Frobenius comparisons here are the iterates of the native sheaf exchange: $j_!$ is extension by zero along the descended open and $p_*$ is precomposition on site objects; [lem-weil-pbc-kinjective-exact-square-comparison] derives those sheaf exchanges, since exact equivalences preserve K-injectives by [lem-weil-pbc-right-adjoint-preserves-kinjective]. Hence for $A\in\mathcal L_X$, the underlying map is precisely
$$\bigoplus_n P_Y^nFA\ \cong\ \bigoplus_n F(P_X^nA)\ \longrightarrow\ F(\bigoplus_nP_X^nA).$$
It is invertible by coproduct preservation; conservativity of $U_Y$ makes $\kappa_A$ invertible. This supplies the induction comparison on all $\mathcal L_X$.

Cited statements: def-sf-native-weil-derived-framework, lem-sf-free-derived-weil-resolution, lem-sf-locally-finite-adic-compact-support-sums, lem-weil-pbc-right-adjoint-preserves-kinjective, lem-weil-pbc-kinjective-exact-square-comparison.

### Original step 5: now owned by lem-sf-native-weil-localizing-brown-adjoints

Choose a set $S_T$ of representatives of $\mathcal C_T$, possible by [lem-sf-locally-finite-adic-constructible-realization], and set $\mathcal L_{W,T}=\operatorname{Loc}(I_TS_T)\subset D(\mathcal W_T)$. Since $I_T$ preserves coproducts and is exact, $I_T\mathcal L_T\subset\mathcal L_{W,T}$. Since $U_TI_TA=\bigoplus_nP_T^nA$, $U_T$ is exact and preserves coproducts, $U_T\mathcal L_{W,T}\subset\mathcal L_T$. Conversely the cyclic triangle of [lem-sf-free-derived-weil-resolution] puts every $K$ with $U_TK\in\mathcal L_T$ in $\mathcal L_{W,T}$. Thus this hull is exactly the full inverse image of $\mathcal L_T$, and contains every native bounded constructible Weil complex. For a family $(K_a)$ in this hull, step 3 identifies $U_Y$ of the coproduct comparison for $F_W$ with the comparison for $F$ on $(U_XK_a)$; it is an isomorphism by [lem-sf-locally-finite-adic-compact-support-sums]. Conservativity gives coproduct preservation by $F_W$. The same forgetful comparison shows $F_WK\in\mathcal L_{W,Y}$.

Cited statements: lem-sf-locally-finite-adic-constructible-realization, lem-sf-free-derived-weil-resolution, lem-sf-locally-finite-adic-compact-support-sums.

### Original step 6: now owned by lem-sf-native-weil-localizing-brown-adjoints

For either $L=F:\mathcal L_X\to\mathcal L_Y$ or $L=F_W:\mathcal L_{W,X}\to\mathcal L_{W,Y}$ and a target $M$, put $H_M(A)=\operatorname{Hom}(LA,M)$, with its abelian-group structure. Exactness gives its cohomological long exact sequences; coproduct preservation gives $H_M(\bigoplus A_i)=\prod H_M(A_i)$. The source is exactly the localizing hull of the set supplied in step 5 (or $S_X$), inside a Grothendieck derived category by step 2. Apply [lem-sfb-set-generated-derived-solution-set] to obtain a small weakly universal family of $H_M$-elements. Its source is idempotent complete by [lem-countable-coproducts-idempotent-complete], since it is triangulated and has countable coproducts. Now [lem-sfb-cohomological-solution-set-representability] makes $H_M$ representable. Finally [lem-sfb-right-adjoint-from-objectwise-representability] assembles these representations into right adjoints $G$ and $G_W$, respectively. All sets, Hom groups and coproducts use the same universe. These ordinary Brown constructions are on the stated localizing categories; they assert no right adjoint on the whole pro-etale derived category.

Cited statements: lem-sfb-set-generated-derived-solution-set, lem-sfb-cohomological-solution-set-representability, lem-countable-coproducts-idempotent-complete, lem-sfb-right-adjoint-from-objectwise-representability.

### Original step 7: now owned by lem-sf-native-geometric-brown-constructible-comparison

For $M\in\mathcal C_Y$, the constructible counit $FG_cM\to M$ of step 1 transposes under $F\dashv G$ to a map $t_M:G_cM\to GM$ in $\mathcal L_X$. For every $A\in\mathcal C_X$ and every integer shift, $\operatorname{Hom}(A,t_M)$ is the composite of the two adjunction bijections and is invertible. If $Q$ is the cone of $t_M$, then $\operatorname{Hom}(A[n],Q)=0$ for every such $A,n$. The objects $B$ with $\operatorname{Hom}(B[n],Q)=0$ for all $n$ form a localizing subcategory: the triangle long exact sequence handles cones and Hom out of a coproduct is a product. It contains $\mathcal C_X$, hence all $\mathcal L_X$. Taking $B=Q$ gives $1_Q=0$, so $Q=0$ and $t_M$ is invertible. Consequently the Brown adjoint $G$ carries $\mathcal C_Y$ to $\mathcal C_X$, as identified with the constructible exceptional adjoint of [lem-sf-constructible-exceptional-adjunction-coefficients] through the two realization lemmas.

Cited statements: lem-sf-constructible-exceptional-adjunction-coefficients, lem-sf-locally-finite-adic-constructible-realization, lem-sf-locally-finite-adic-compact-support-realization.

### Original step 8: now owned by the item assembly, steps 3-4

For $M\in\mathcal L_{W,Y}$ and $A\in\mathcal L_X$, the exact free adjunction and the actual induction comparison of step 4 give natural bijections
$$\begin{aligned}
\operatorname{Hom}(A,U_XG_WM)&\cong\operatorname{Hom}(I_XA,G_WM)\\
&\cong\operatorname{Hom}(F_WI_XA,M)\\
&\cong\operatorname{Hom}(I_YFA,M)\\
&\cong\operatorname{Hom}(FA,U_YM)\\
&\cong\operatorname{Hom}(A,GU_YM).
\end{aligned}$$
Both represented objects lie in $\mathcal L_X$ by step 5, so these bijections give $U_XG_WM\cong GU_YM$, naturally in $M$. Explicitly evaluate the bijections and their inverses at the two identity maps to obtain mutually inverse arrows; their composites are identities by naturality. If $M$ is a native Weil complex, $U_YM\in\mathcal C_Y$ and step 7 gives $U_XG_WM\in\mathcal C_X$. The native definition therefore puts $G_WM$ in $\mathrm{WC}_{\mathrm{der}}(X_0)$. No faithfulness of the derived forgetful functor is required here.

Cited statements: lem-sf-free-derived-weil-resolution, def-sf-native-weil-derived-framework.

### Original step 9: now owned by the item assembly, steps 3-4

Step 1 shows that $F$ preserves $\mathcal C$. Together with step 3 this puts $F_WK$ in $\mathrm{WC}_{\mathrm{der}}(Y_0)$ for every native Weil complex $K$. Restrict $F_W\dashv G_W$ to these two full subcategories, using step 8 for the right functor. Their Hom sets are the ambient derived Hom sets, so the same natural bijection $\operatorname{Hom}(F_WK,M)\cong\operatorname{Hom}(K,G_WM)$ is the required adjunction. By the native definition its left functor is exactly Lean `WeilComplex.derivedLowerShriek` for the chosen compactification. This proves `HasUpperShriek` and allows its chosen right adjoint `upperShriek`, with every original scheme hypothesis retained.

Cited statements: def-sf-native-weil-derived-framework.


## First repaired dry-run diagnostic

The first dry run of the repaired split exited 1 before server preflight because its Stacks 070Y source overlaps eleven additional existing nodes. I opened and read all eleven statements; none states the native compact-support/free-induction comparison. The Not duplicates section now contains one explicit distinction per pair. No mathematical statement or search was changed for this packaging repair.
