# Brief for a stage-1 worker of a remote group (direct delivery)

You split ONE item of the DAG of the Weil SHEAF project (new targets, in the live repository) and deliver it yourself. No second worker reads it: when the dry run passes you push it yourself, and the maintainer's independent review reads the delivery. Your group is GROUP, your item is ITEM.

## Where things are (this machine)

- The repository, read-only for you: /home/ubuntu/weil-conjectures-sheaf-GROUP (the DAG in dag/nodes/, the contract, the literature). Never write there and run no git command there.
- The Lean source of the project, read-only: the library in your read clone, /home/ubuntu/weil-conjectures-sheaf-GROUP/lean (WeilConjectures/ and Sheaf/, exactly the live project; Mathlib under lean/.lake/packages/mathlib/Mathlib/).
- Your sandbox, the only place you write: /home/ubuntu/weil-newtargets-sandbox/GROUP/ITEM/ . Node files go to dag/nodes/<chapter>/<id>.json under it (same relative paths as in the repository), your report to report.md.

## What to read first, in the repository

coord/brief-stage1.md (the worker's rules and the report format), stages/1-dag.md, the three levels in SETUP.md, and coord/delivery-errors.md sections B to E: every reason deliveries were returned for, with real cases. Read B to E whole; they are the checklist of this brief.

## The work

1. Before starting from an empty sandbox, inspect earlier abandoned attempts of this same item. The dispatcher archives them outside the active sandbox at `/home/ubuntu/weil-launcher-all/abandoned/<group>/ITEM.<timestamp>/`, including attempts by other groups. This path is an explicit read-only exception to the search-directory restriction below. List matching directories with `python3 -c 'from pathlib import Path; print("\n".join(str(p) for p in sorted(Path("/home/ubuntu/weil-launcher-all/abandoned").glob("*/ITEM.[0-9]*"))))'`. Read their report.md and searches.jsonl, newest first, and any item-specific route note. Compare the archived item with the live statement before reusing it. Copy useful evidence into your own sandbox without modifying the archives or overwriting current work. Keep the original search records and attribution; do not present them as searches you ran. Repeat a failed construction only when you can identify a new step that addresses its recorded obstruction. Then, if the sandbox has no item node, copy it from the repository and work on the copy. If an earlier attempt already wrote the item, continue that copy: compare it with the current repository, retain its proof, report, citations and logged searches, and update only what changed. When a split and report are already present, run the required dry run in step 6 first; use its diagnostics to decide what needs repair. A missing final answer or an API/transport failure does not invalidate completed work. Reuse searches recorded in searches.jsonl after reading their results; repeat them only when the statement or the search question changed.
2. Is it already done? Search the Lean source for a declaration that states the item exactly (grep -rn in WeilConjectures/ for the notion and for the docstring tag "(blueprint: ITEM)"). It must be a declaration of the project (under WeilConjectures/), with no `sorry` in its proof, that gives every clause of the item under hypotheses the item has. If so, do not split: answer "ATTACH ITEM: <full declaration name with namespaces>[, <further full names>], <file>:<line>" and stop; a second worker tests the claim and a tool checks that nothing below it is sorried. A declaration that has sorry, or proves only part of the item, is not an attachment: split the item. A declaration of Mathlib is not an attachment either: the item is then a Mathlib leaf (step 3) and is delivered as one.
3. Split the item as coord/brief-stage1.md says: the proof in steps, every non-elementary fact a cited node, sources by Stacks tag. Before creating any node search the whole DAG and blueprint for an existing one (grep -rl on dag/nodes, tools/blueprint_refs.py search) and the Lean source; cite what exists. A new node that you do not split carries a statement only. Fill the `blueprint` field (from.place, same_as) of the item and of every new node.
   **Mathlib searches are made only with the search command, and recorded as they came out.** For every node you create (and for the item, if it might itself be in Mathlib) run, with the node's own id as you will name it in mind:
   `python3 /home/ubuntu/weil-launcher-all/batch2/msearch.py GROUP ITEM leanfinder "<the statement in plain words>"`, `... loogle "<a Loogle pattern: the Mathlib names you expect, comma separated, e.g. Polynomial.Separable, Multiset.Nodup>"`, `... grep "<regular expression>" [<subdirectory of Mathlib/>]` (and `... leansearch "<plain words>"`, which is down at times; the command says so). Read the hits. Try a second phrasing before you conclude there is no match: Mathlib states things more generally and with other names than the source. If a hit states the node, or the node is a one-line specialization of it, the node is a Mathlib leaf (status mathlib, the declaration, its file and line from the grep). In `mathlib_searches` write exactly the searches you ran (same tool and same query text) with a verdict; a service that was down is recorded as "unavailable". The delivery tool compares them with the log the command keeps and refuses to push a new node whose searches were not run. Writing a search you did not run is the one thing that gets a group stopped.
   **What is NOT a new node.** An audit of 40 nodes created by remote workers found 23 that should not exist. Before you create a node, rule out all three:
   - *Elementary (9 of 40).* A fact you can prove in two or three lines from statements you cite and from definitions is a STEP of the item's proof, marked elementary or citing those statements, with the argument written out; it is not a node. Returned as nodes: "a finite product of left exact sequences is left exact"; "L^n is locally O, so F ⊗ L^n is quasi-coherent"; "F = i_* i^{-1} F on its support, then apply the two cited vanishing lemmas". A step may name a Stacks tag in its text without a node when the step itself proves the fact.
   - *Duplicate (9 of 40).* Search dag/nodes for the Stacks tag of the fact (grep -rl "<tag>" dag/nodes) and for its key words. If a node states it, or states something more general of which yours is a special case, cite that node. The delivery tool lists every existing node with the same tag and refuses to push until report.md has a section "## Not duplicates" with one line per pair, "<new id> vs <existing id>: <how the statements differ>".
   - *A clause of the item itself (5 of the 9).* A new node that restates the item, or one clause of it, so that the item's proof becomes "apply the new node", is not a split (delivery-errors D1, D2). The steps of the item carry the argument.
   - *Already in Mathlib (5 of 40).* That is what the searches above are for: general category theory, homological algebra and commutative algebra facts are usually there under a more general statement.
4. Check your own work against coord/delivery-errors.md B to E, point by point, with the node files and the sources open; test every new statement on its small cases; repair what fails. Two faults cause most returns (two thirds of them), so check these for every step:
   - **A cited node must say what the step takes from it (C4).** Open the file of every node the step cites and read its statement. Returned: the general Yoneda lemma Hom(h_A, F) = F(A) used, but the cited node states only that h is fully faithful; a colimit taken over a category that is not small, while every cited existence node assumes a small index category; a definition node cited for a theorem about the notion.
   - **Every fact a step uses that is not elementary is a cited node (C1).** Returned: "since M ⊗ A is flat, tensoring this exact sequence preserves exactness" with only the definition of flatness cited. If no node states the fact, create a statement-only node for it (after searching the DAG, the blueprint and the Lean source) and cite it.
   Then write citations.json in the sandbox: a list with one entry {"step": n, "node": "<id>", "quote": "<verbatim sentence or formula copied from that node's statement, the part this step uses>"} for every node cited by every step of the item (steps numbered from 1). The delivery tool refuses to push unless every quote is a verbatim part of the cited node's statement. If you cannot find such a sentence in the node, the node does not say it: that is C4, repair the split, do not bend the quote.
5. Write report.md: the worker's report of coord/brief-stage1.md, and a section headed exactly "## Review by GROUP" in which you say, in your own words, what you checked in step 4: which source you read for the item and for each new node, for each step which cited statements it uses and that they say it, which hypotheses you verified where, and what you corrected. It is your signature under the split; a list of mechanical checks is not enough.
6. Dry run: python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py GROUP ITEM --no-push . It builds the commit and runs the maintainer's preflight, tools/check_dag.py and tools/review_split.py included, on the Weil server. Repair every failure it lists in the sandbox and run it again until it prints OK. Before report.md is written, `python3 /home/ubuntu/weil-launcher-all/srvcheck.py weil-conjectures-sheaf GROUP ITEM check_dag` (or `review_split`) runs one of the two checks there on the sandbox. Never run tools/check_dag.py, tools/review_split.py or tools/preflight_delivery.py on this machine.
7. Deliver: python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py GROUP ITEM .

Keep one deliver.py invocation active for this item. When it waits, poll the same tool session until the process exits; do not launch another dry run or push. `DELIVERY ALREADY RUNNING` (exit 75) means the duplicate was rejected before admission: wait for the original command. Wait for the final dry run to exit before pushing.

## Your answer to the lead, one of

- "DELIVERED ITEM at <commit>: <n> new nodes, <m> Mathlib leaves" (the push printed DELIVERED) ;
- "ATTACH ITEM: ..." (step 2) ;
- "ABANDON ITEM: <what is wrong with the item or what you could not prove>" ;
- "BLOCKED ITEM: <the tool failure>".

If this is a repair of a returned delivery, the lead gives you the return entry: repair every numbered point, then steps 4 to 7 again and answer DELIVERED.


Human decision 2026-10-14: only stage 1. Never write Lean or run any compiler/Lake/build tools. Never write to the repository or the launcher. Read GOAL.md. The upstream Lean source is the library in your read clone (lean/WeilConjectures/); its sorry declarations are not finished proofs. Your sandbox is the only place you write. Do not start agents.

## Statement disputes are repaired, never abandoned

If the imported statement is ill-typed, false, or missing hypotheses, mark `STATEMENT-DISPUTED` in report.md, give the explicit counterexample or type check, correct the statement faithfully to the source's intent, and continue the split. Answer DELIVERED only after the corrected split passed the dry run and was pushed, or BLOCKED. ABANDON is reserved for a node that genuinely cannot be split after the whole time budget.


## The shared repository (launcher, 2026-10-16)

The repository you read is shared by all groups and is read-only for you. The delivery tools (deliver.py, deliver2.py, deliver3.py, also with --no-push) build the delivery in their own temporary git worktree; running them is the required step, not a forbidden git command. If one reports that a delivery branch is checked out in another worktree, run it again once; report BLOCKED only if it persists. A delivery tool that has to wait waits by itself; do not look at lock files (lsof, fuser). Search only in the directories this brief names, never in the home directory or in /.

## Route lock: no SGA (the human and the project's expert, 2026-10-16)

Do not use any SGA source except SGA 5 for the Lefschetz–Verdier pairing. In particular, finite-coefficient smooth purity follows the blueprint's lecture-notes route (diagonal class and deformation to the normal cone: `thm-pur-finite-coefficient-smooth-purity`, `thm-pur-diagonal-dualizing-object`, `thm-pur-dnc-invariance`, `thm-pur-affine-line-purity`, `thm-pur-finite-reduction-of-purity`), never the SGA 4 XVIII trace route. Cite blueprint, Stacks, Bhatt–Scholze or the other literature instead. The preflight refuses a split that cites SGA 4 or SGA 4½.

## The current blueprint (2026-10-16)

The current blueprint is `literature/blueprint/latest/`: always the newest weil-conjectures-blueprint main (refreshed daily; the snapshot it points to is named in `literature/blueprint/COMMITS.txt`). Read the blueprint there, never an older snapshot directory. A DAG node whose blueprint text changed carries `blueprint_update` with the newest statement.


Long steps (the human, 2026-10-17): the review mechanically lists every non-elementary proof step longer than 2000 characters and the reviewer then checks whether it hides a lemma (a sub-claim with its own hypotheses, a comparison or identification proved inline, an argument the source calls standard). Before delivering, look at each such step yourself: if it hides a lemma, make that lemma a node of its own and cite it; keep a long step only when it is genuinely one routine argument.


## Launcher files (launcher, 2026-10-18)

The launcher's own files (every script under /home/ubuntu/weil-launcher, /home/ubuntu/weil-launcher-nt and /home/ubuntu/weil-launcher-all, including their permissions) are not to be edited, copied into a patched private copy, or marked assume-unchanged: an edit is reverted automatically within minutes and the run is flagged in an incident log, and a gate or tool that seems wrong is reported in your answer as BLOCKED with the reason, never patched or worked around.
