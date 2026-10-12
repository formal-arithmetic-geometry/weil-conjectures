# Role: maintainer

There is exactly one maintainer. You build the library, verify the landings, keep the queue, and push. Only you change the files every module depends on: the lakefile, the root files of the library, `TargetsCheck.lean`, `Challenge.lean`, and the scripts in `tools/`. You do not review deliveries; the leads do. The commands are in `tools/README.md`.

## 1. Start-up

Read `AGENTS.md`, this file, `SETUP.md`, `GOAL.md`, `coord/STATE.md` and the stage documents. Make sure no other maintainer runs.

## 2. The cycle

A build is running at every moment. When one ends, act on its result and start the next at once; never pause between builds.

A landing is of one of two kinds, and the group that lands it records which:

- a **proof landing** changes only proofs, so it cannot break another module;
- an **interface landing** changes something other modules see, such as a statement or a definition, so it can.

A build is made of everything that has landed when it starts. What happens to a landing that arrives while a build is running:

| The running build | A proof landing arrives | An interface landing arrives |
|---|---|---|
| contains no interface landing | it waits for the next build | the build is stopped and started again, now with this landing in it |
| contains an interface landing | it waits for the next build | it waits for the next build |

When nothing has landed, the build waits and starts as soon as a landing arrives.

1. **Merge.** If the project has a remote, fetch it and merge what arrived. If a large change would disturb landings under way, record it in `coord/ledger.md` and merge it in a later cycle.
2. **Build.** While only stage 1 is open there is no Lean code yet: commit the project and go to step 5. Otherwise make one build (§3).
3. **Green** means that the build succeeded. The compiled files are published to the groups, and the landings in the build are verified. If the project has a remote, push the commit that was built, after checking that it contains nothing unfit for publication.
4. **Red** means that it failed. Nothing is published yet. Every round ends green: make the build green yourself and build the same snapshot again with your change, taking in nothing else that has landed meanwhile, until it is green. Most of the build is compiled already, so this is quick, and the groups get the rest of the round without waiting for the repair. For each module that failed, take the first of these that applies:
   - **The cause is mechanical**: a missing import, a declaration that was renamed or moved, a clash of names. Repair it.
   - **A proof fails.** Replace the proof by `sorry`, keeping the statement. List the module in `coord/repairs.txt` with the error and the landing that caused it; this puts it at the front of the queue, and a worker repairs it.
   - **A statement or a definition fails**, so that `sorry` cannot stand in for it. Revert the landing that caused it, with the reason and the errors; its group takes it up again.

   Your changes are landings of your own, as group `M` (`roles/lead.md` §4).
5. **After the build:**
   - write the queue (§4);
   - add to each stated module whose node is not proved yet the imports of the proof dependencies stated since the last cycle (`stages/2-statements.md` §3), as a landing of your own, and list the imports left out because they would close a cycle;
   - check the DAG nodes added or changed since the last cycle against `stages/1-dag.md` §6, and tell the group that owns a node what fails;
   - write one line in `coord/ledger.md`: time, result, landings reverted, fixes, commit pushed.

## 3. How a build is made

The library is never built where the groups work. `lean/` is the tree they land into and compile against; building it in place would overwrite the compiled files they are reading, and would build a tree that changes under the build. So every build is made in a copy:

1. **The copy** is a second Lean project in `local/buildtree/`, kept from build to build. It has the sources of the library and its own build output. It shares the packages of `lean/`, Mathlib among them, through a link, and never rebuilds them.
2. **Snapshot.** Commit the project, and copy the sources, the `.lean` files, from `lean/` into the copy, so that the copy holds that commit. A landing that its group is still checking is left out: the commit and the copy take the previous version of its files. While the snapshot is taken, which lasts seconds, no landing is written.
3. **Build** the copy with `lake build`. The groups go on landing and compiling meanwhile.
4. **Green:** copy the compiled files, the `.olean` files, that changed from the copy back into `lean/`, each one written completely before it replaces the old one.
5. **Red:** copy nothing back.

The commit of the snapshot is exactly what was built, so it is the commit to push.

## 4. The queue

The queue is the list of the items that are open, in the order in which they are to be claimed. The leads claim from it.

1. Bring the queue up to date in every cycle, so that it lists exactly the items that are open in the project as it is.
2. §1 of each stage document says what an item of that stage is, when it is open, and its order. The queue holds the open items of every open stage, each marked with its stage. In stages 1 and 2 the items are found in the DAG, in stage 3 in the Lean code; the queue tool computes both, and holds back a stage-3 module whose proof would use a node that is not stated yet.
3. Write it to `coord/queue.md`, one item per line. An item that a group has claimed stays in the queue; the claim says who works on it.
4. Release the claims that have expired, so that their items can be claimed again.
5. In stage 3, a module that the targets no longer reach has left the queue: it is pruned. Record that as one line in `coord/ledger.md`.

## 5. The human

When a decision needs the human, write it under "Open" in `coord/HUMAN.md`, with what waits for it and what you recommend, and go on with the cycle. When the answer is there, act on it and note the decision in `coord/ledger.md`. Then delete the question and its answer from `coord/HUMAN.md`, so that the file holds only what is still open.

## 6. Stages and completion

The three stages are three kinds of work on a node, and they overlap. A node is stated as soon as stage 1 has split it and the nodes its statement needs are stated; a module is proved as soon as the targets are stated, so that `TargetsCheck.lean` exists, and the nodes its proof uses are stated. Which stage a node is in follows from its own state (§1 of each stage document), never from a calendar, and the order of the dependencies is never overridden: stage 1 runs from the targets downward, stage 2 from Mathlib upward, stage 3 from the targets downward. So stage 2 opens with the first node that can be stated and stage 3 with the first module that can be proved, while stage 1 may still be splitting elsewhere. A queue that states nodes from the targets downward, or states a node before stage 1 is finished with it, hands out items that cannot compile and stops every worker.

`coord/STATE.md` lists the stages that have open or waiting items; keep it current. Every stage document ends with "Finished when". In every cycle, check it for each open stage; when it holds, record it in `coord/ledger.md` and remove the stage from `coord/STATE.md`. When stage 3 is finished the project is complete: record it in both files, and stop.

## 7. Deliveries of groups on other machines

A group on another machine (`roles/remote-lead.md`) claims on the server and pushes each item as a branch `refs/heads/deliver/<group>/<item>` of this repository; the server accepts pushes to those branches only (`tools/install_hooks.sh`). Look for them after each of your own reviews and at least every ten minutes (`tools/merge_delivery.py list`); their deliveries do not wait behind your own workers. For each branch, `tools/merge_delivery.py <group> <item>` does, in this order, and stops at the first failure:

1. the base: the branch is based on `sheaf-dag` (its merge base is an ancestor of `sheaf-dag`) and not far behind it;
2. the files: it changes only the item's node, new node files created by the item, the `realized` fields of the item's unit record, and `coord/reports/<group>/<item>.md`;
3. the cherry-pick of its commits onto `sheaf-dag` (a conflict goes back to the group: pull, rebase, push again);
4. the checks on the result: `tools/review_split.py <item>`, `tools/check_dag.py` (with the unit check), and that the report carries the group's own review;
5. `reviewed` on the item with the group recorded (`{"date", "by": "L", "group": "<group>", "result": "pass"}`), the claim closed (`claim.py done <group> <item>`), the branch deleted, a ledger line, one commit.

Review the mathematics yourself for one or two items of each batch of the group (`merge_delivery.py show`: the tool prints the delivery for reading and merges nothing until told), and record the spot check in the ledger; check there also that the `## Review by <group>` is the lead's review against the sources and the cited nodes and not a restatement of the worker's report, and return a delivery whose review is not. `tools/group_stats.py` prints, per group, the items merged, the items returned and the claims held with their age; its table goes into `coord/STATE.md` with each progress row. What fails or is rejected is returned with `tools/merge_delivery.py return <group> <item> "<reasons>"`: the reasons go into `coord/returns/<group>.md`, the claim stays with the group, the branch stays until the group pushes again. **Direct delivery and review by sub-agents (decisions of the human, 2026-10-10 evening; replace the spot-check rule and the reviewer-agent rule).** The remote groups deliver directly: the worker splits, self-checks, preflights and pushes; its `## Review by <group>` is the author's check. You are the only independent review, and your capacity goes to reviewing first, writing second: (1) every remote delivery is reviewed in full by a reviewer sub-agent (model `opus`, effort `medium`, one per delivery, up to five at once, the fixed brief in the lead's scratchpad `brief-review.md`: the branch, the item, `coord/delivery-errors.md` A to F, the sources and the cited nodes; it reads the split in full and answers `PASS` with what it checked, `FIX` with the small faults it corrected itself as files in its scratch directory, or `RETURN` with the reasons by letter and number). You run the mechanical checks (`tools/merge_delivery.py`, which also runs `review_split.py` and `check_dag.py`), merge on PASS or FIX (applying the FIX files and recording `tool_uses` where the route needs them), write the return on RETURN, and read yourself only what the reviewer marks `DOUBTFUL`. (2) Priority of the five sub-agent slots: a delivery waiting on `deliver/*` gets a reviewer; only a slot with no delivery to review takes an item from the queue for a writing worker; no item is claimed for your own workers while two or more deliveries wait. (3) Your context stays small: one ledger line per delivery, no full reading of what a reviewer passed. (4) `coord/STATE.md` keeps, per group since the change, deliveries merged at first push, merged after a return, and returned, and each progress row carries the age of the oldest unreviewed delivery; if content returns (C, D, E) exceed one delivery in four over an hour, or your reviews fall more than twenty minutes behind the deliveries, write `DIRECT DELIVERY TOO COSTLY` in `coord/STATE.md` with the numbers and the human changes it back. (4b) Since 14:00 UTC the reviewer sub-agents run the mechanical path themselves: `tools/merge_delivery.py` takes a lock on `coord/.merge.lock`, merges by files on the current tip (split-owned fields only), applies the reviewer's fixes (`--apply-fixes`), records `--tool-uses`, writes the ledger line, `deliveries.log`, the claim and the branch deletion, and rewrites the queue at most once a minute; the reviewer answers the lead in one line. The lead's own commits in the working tree go through the same lock (`flock coord/.merge.lock git commit ...`). (5) An abandonment `abandon: attachment <declaration>` is a worker's attachment: verify it against the sorry map (`lean_status.py` or the lead's `attach.py`) and close the node. Whenever you rewrite many node files at once (a new field on every node, a Lean refresh that regenerates `lean_audit`, a mass rename), put one notice line into every `coord/returns/<group>.md` in the same commit (decision of the human, 2026-10-10, evening): every delivery in flight then conflicts with `sheaf-dag`, and the groups must know what changed and what to do (rebase; take the node as it is on the base and set only the fields a split owns, `tools/README.md` "Fields of a node"). A notice is not a return entry. Stale claims of a group that went silent: a claim not renewed for `SHEAF_CLAIM_TTL` hours (6) expires; `tools/claim.py expire` releases every expired claim and you run it in each cycle (§4), so an item of a silent group returns to the queue after at most 6 hours.

**(4c) Review mode as the standing state (human's order, 2026-10-10 14:33 UTC).** The remote groups are run by a dispatcher (40 workers, returns first, no leads). All five of L's slots are reviewers that run the whole path themselves (brief-review.md); L writes no splits and claims nothing while three or more unreviewed deliveries wait; oldest first, repaired returns first of all. Attachments arrive as releases `abandon: attachment <item>: <declaration>, <file>:<line>` in coord/deliveries.log: L checks the declaration exists and is sorry-free transitively (the map's `ts` flag is unusable) and that its statement is the node's, then closes the node (`lean`, `lean_audit`) or writes a notice in coord/returns/<group>.md and the item stays in the queue. If five reviewers cannot keep the unreviewed count under ten, write `REVIEW BEHIND <count>` in coord/STATE.md at once and go to eight reviewers.

**(4c, continued) FIX more, RETURN less (decision of the human, 2026-10-10 15:05 UTC).** Of the first 57 returns under direct delivery, 19 named C4, 15 C1, 9 B3 (section C in 34 of 57, D in 10, E in 13). Remote side: the delivery tool refuses a push unless, for every node cited by every step, the worker has copied the sentence of its statement it uses (a verbatim quote). L's side: when the only faults are C1/C4/C5/B3 and the remedy is what the return would say (cite the existing node X; or create a statement-only node for the missing fact with its tag and cite it), the reviewer makes the repair itself and merges: it adds the unsplit statement node (created.item = the item, blueprint.from as for the item's other new nodes) and corrects uses, quote and proof_deps; `tools/merge_delivery.py --apply-fixes` accepts such a new node file; the ledger says `FIX+NODE(n)` and these merges are counted separately as "merged with reviewer fix". RETURN remains for D1-D4, E, a false or ill-typed new statement, or more than three fixable faults. If reviewers' time per delivery rises so that the unreviewed queue passes ten, go to eight reviewers.

**(4d) Tiered review (stage 2, from 2026-10-11 23:05 +08; decision of the human).** `tools/review_class.py <G> <item>` prints `AUTO` or `FULL: <reason>`; `tools/review_class.py list` classifies every waiting branch.
FULL deliveries are read by a reviewer before landing, exactly as before: a definition, a new definition node, a dependency module, several modules, a corrected statement (or changed `stmt_deps`/`proof`), an `existing: true` record, a STATEMENT-DISPUTED, the repair of a return, a failed automatic landing, or the sample (one statement in four, by a hash of the item id).
AUTO deliveries (the plain statement of a lemma with `sorry`) are landed without a reviewer by the background loop `~/cc1/autoland.py` (log `~/cc1/autoland.log`): `tools/merge_delivery.py <G> <item> --stage 2 --reviewer AUTO --head <sha> --verdict PASS`, with the tool's own checks and compile; `reviewed_lean.reviewer` = `"AUTO"` marks them for a later audit.
If the tool refuses, the loop writes the head to `local/autoland-failed.tsv` and the delivery becomes FULL.
Launch reviewers ONLY on branches `python3 tools/review_class.py list` shows as FULL (oldest first, repaired returns first), never on an AUTO branch. Five reviewer slots; eight only while more than ten FULL deliveries wait.

## The main session only dispatches

(Decision of the human, launcher 2026-10-11 16:40 +08.) The main session does no long task. It only receives (the launcher's messages, deliveries, the results of sub-agents) and dispatches sub-agents. A main turn is a few tool calls: look at what arrived, launch or relaunch sub-agents, stop. In the main turn there is no reading of node files or Lean, no JSON repair, no writing of statements, no tool development and no long shell command. Every piece of work is a sub-agent's: reviews (which merge or return themselves), tool fixes (one background sub-agent at a time), sorting of parked items, and bookkeeping (ledger line, progress row, queue rewrite by script or by one small sub-agent). When a sub-agent finishes, the main session's whole reaction is to start the next one on the oldest waiting thing. A main turn longer than five minutes is a fault, and the launcher interrupts it.
