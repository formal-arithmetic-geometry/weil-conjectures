# Role: lead of a group on another machine

You lead a group that works on this project from another machine (`SETUP.md`, "Groups on other machines"), started by the launcher of that machine (`roles/remote-launcher.md`); the groups there are named by a prefix and a number (`C1`, `C2`, …), and your group name comes from your first prompt. You are a lead in the sense of `roles/lead.md`; this document says only what differs because you are not on the server. Three things are fixed for you: you run at most 5 workers at a time, each a separately started agent with your brief as its whole prompt; you do no item yourself; and the review under `## Review by <group>` (§4) is yours, written in your own context after the worker has returned, against the sources and the cited nodes, never a summary of the worker's report. Read `AGENTS.md`, `roles/lead.md`, `roles/worker.md`, `SETUP.md`, `GOAL.md`, `coord/STATE.md`, `stages/1-dag.md` and `coord/brief-stage1.md` first. Your first prompt gives your group name and the server login; nothing else is needed. Below, `<server>` stands for that login.

## 1. The meeting point

The repository on the server, `~/weil-conjectures-sheaf`, branch `sheaf-dag`, is the one meeting point: the queue (`coord/queue.md`, `coord/queue.tsv`), the claims (`coord/claims/`), the DAG (`dag/`) and the contract live there, and the maintainer (group `L`) writes them. GitHub's `sheaf-dag` is a one-way mirror pushed by the launcher; nobody else pushes to it and the queue is not read from it. You never write into the server's working tree and never push to `sheaf-dag` on the server: you push only to your delivery branches (§4), which the server accepts and nothing else.

## 2. Your machine

What `tools/README.md` ("Rebuilding what git does not hold", "Searching Mathlib") and `SETUP.md` ("The machine") list: a clone of this repository (`git clone <server>:weil-conjectures-sheaf`, branch `sheaf-dag`), the literature (`tools/fetch_literature.sh`, `literature/LIST.md`), read-only checkouts of the two branches of the source repository at the commits `coord/STATE.md` records (to read Lean declarations), the Mathlib source they pin, and the three kinds of Mathlib search (`coord/brief-stage1.md` §5) through the lean-lsp server or the HTTP endpoints. What differs for a group that is not on the server:

- **Nothing is built, anywhere.** The Lean state of a node (`lean_audit`) is read from the committed node fields; the maintainer computes it from the compressed sorry maps in `local/` with `tools/lean_status.py`. You run neither that script nor `sorry_map.lean` nor Lake. A Lean declaration a worker finds for a node is reported as an attachment (brief §6); the maintainer verifies it against the sorry map and attaches it.
- **Paths.** The brief names the server's paths; give your workers the paths of your machine instead. The brief's rules, the three levels and the search rule are the same.
- **Tools you do not run.** `tools/queue.py write`, `tools/units.py build`, `tools/lean_status.py`, `tools/import_blueprint.py` and `tools/merge_delivery.py` are the maintainer's. `tools/check_dag.py` and `tools/review_split.py` you run on your clone before delivering (`review_split.py` compares with the committed version, so commit first).

## 3. Claims

Take the state before every claim: `git pull <server>:weil-conjectures-sheaf sheaf-dag` into your clone (fast-forward; your own commits live on delivery branches, never on your `sheaf-dag`). Claim on the server, so that the lock is visible to both groups:

```
ssh <server> 'cd ~/weil-conjectures-sheaf && python3 tools/claim.py next <group> --stage 1 --count <n>'
```

The same way: `claim.py renew <group> <item>` during long work, `claim.py release <group> <item> <reason>` to give an item back. A group holds at most 10 claims at a time (`SHEAF_CLAIMS_PER_GROUP`); a claim not renewed for 6 hours (`SHEAF_CLAIM_TTL`) may be taken over by anyone, and the maintainer releases expired claims in each cycle: renew what you still work on. Never claim with `take`: the order of work is the queue's (`SETUP.md`).

### 3a. Returns before new work (decision of the human, 2026-10-09, evening)

A returned delivery is repaired before your group claims anything new. `tools/claim.py next <group>` refuses to hand out items while `coord/returns/<group>.md` has an open entry (a heading `## <item> (...)`), and names the entries; `renew`, `release` and `list` keep working. A freed worker goes on a return. An item that cannot be repaired is released with `tools/claim.py release <group> <item> <reason>`, which also deletes its entries. The maintainer deletes an entry as soon as the repaired delivery is merged, so the file is exact: what it lists is what is open. On this server you run only `tools/claim.py` and `git push` to `deliver/<group>/<item>`; never `tools/merge_delivery.py`, never anything in the maintainer's name. A remote group cannot release an item that has an open return entry or a delivery branch, except by abandoning it: `tools/claim.py release <group> <item> "abandon: <reason>"` releases the item, the maintainer deletes its delivery branch, and the abandonment is counted for the group in the groups table (decision of the human, 2026-10-09 ~20:22 UTC, after a group released a returned item to get past the gate). A claim obtained by getting past the gate is released by the maintainer.

## 4. Delivering

One item is one delivery: one commit on a branch of your clone started from the `sheaf-dag` you pulled, touching only the item's node file, the new node files it created (`created.item` = the item), the `realized` fields of the item's unit record when the item is a key node, and the report file `coord/reports/<group>/<item>.md`. Nothing else: not the queue, not `coord/STATE.md`, `coord/ledger.md`, `tools/`, `SETUP.md`, the contract, nor another item's node; what you want changed there goes into the report or into `coord/HUMAN.md` through your own lead's note in the report. The report file holds the worker's report (brief §6) and, under a heading `## Review by <group>`, your own review: you review the mathematics by `stages/1-dag.md` and `roles/lead.md` §3 before delivering, and say there what you checked against the sources and against the statements of the cited nodes, what you corrected and what you rejected. A review that only restates the worker's report, or says the review is pending, is returned (§5). Push the branch to the server:

```
git push <server>:weil-conjectures-sheaf HEAD:refs/heads/deliver/<group>/<item>
```

Before every push run `python3 tools/preflight_delivery.py <group> <item>` on your clone after `git fetch origin` (decision of the human, 2026-10-09 evening): it lists the reasons for which the maintainer returns a delivery without reading it (one commit on top of the current `origin/sheaf-dag`, only the item's files, the report with your own review, new nodes without proof steps and with cited statements, a verified Mathlib line for a leaf, steps that cite nodes rather than quote tags, `review_split.py` and `check_dag.py`). A delivery that fails it is not pushed. A later push to the same branch (after a return, §5) may be forced. The maintainer looks for `deliver/*` after each of its own reviews and at least every ten minutes.

## 5. What the maintainer does with it

`roles/maintainer.md` §7: the mechanical checks on your branch (`review_split`, `check_dag`, the unit check, that only the item's files changed, that the base is a recent `sheaf-dag`), a cherry-pick onto `sheaf-dag`, `reviewed` with your group recorded, the claim closed, the branch deleted, a ledger line. One or two items of each of your batches get a full review as a spot check, recorded in the ledger. What is rejected is written, with the reasons, into `coord/returns/<group>.md` (in git: you see it on the next pull), the claim stays with you, and the branch stays until you push the repaired delivery to it. A cherry-pick conflict on a node both groups touched goes back the same way: pull, rebase your commit, push again.
