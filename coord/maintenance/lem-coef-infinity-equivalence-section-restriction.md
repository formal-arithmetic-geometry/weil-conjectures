# N1 section-restriction pipeline maintenance, 2026-10-17

Item: `lem-coef-infinity-equivalence-section-restriction`, stage 1,
project `/home/ubuntu/weil-newtargets`, dispatcher key `<item>@new`.

## Cause

All five counted post-READY failures (second-reader 1792194097 and authors
1792195322, 1792196280, 1792196368 and 1792196673) terminate in
provider HTTP 429. Attempt 1792196368 explicitly reports
`gateway_concurrency_limit: Concurrency limit exceeded for account`. The later
1792196673 attempt fails the same way. Dispatcher NOANSWER lost that diagnostic.
The dispatcher launched a fresh author after the interrupted second reader.
Earlier attempt 1792192813 had already passed server preflight at f1beb6ce17;
the second reader wrote its audit before the provider failed. There was no
server return, delivery branch or landing failure for this item during diagnosis.

An independent persistence defect amplifies this: config includes N1 in both
batch1 (live) and batch2 (isolated). Each Group loaded its own dictionary but
both saved to `run/N1/state.json`. At 08:30 the file contained only live-project
records and no trace of this item's running PID 2490152, stage, tries or notes,
although that timeout/Codex process was still working on the isolated item.
The same collision exists for N2, N3 and N4. This is a pipeline failure, not
evidence that the imported mathematical statement needs alteration.

## Changes

- `tools/launcher/group_state.py`, installed beside the launcher dispatcher:
  separate `state-batch1.json` and `state-batch2.json` within each group directory.
  On first migration, retain legacy history without resetting counters, identify
  own-project surviving/completed records, and adopt missing live workers from
  an exact CLI/output-path match. Never rewrite the legacy file or signal a PID.
- `tools/launcher/dispatch_all.py`: use the project-specific state loader and name
  the actual state file in maintenance prompts. Other maintenance edits retained.
- `tools/launcher/stale_deliveries.py`: the installed side-project monitor reads
  batch2's private state, with fallback before migration.
- `tools/launcher/test_group_state.py`: nine regression checks, including the
  real dispatcher constructor, cross-project writes, missing-PID recovery,
  completed records, count preservation, return key/role and legacy isolation.
- `tools/launcher/group-state.md`: deployment and migration documentation.
- `tools/launcher/route-notes/lem-coef-infinity-equivalence-section-restriction.md`,
  also installed in `/home/ubuntu/weil-launcher-nt/route-notes/`: retained-work
  handoff for the next author and independent reader.

Existing files changed by this maintenance have adjacent
`.maint-N1-section-state-1792196975.bak` backups. New files have no prior contents.
Server commit is made under `coord/.merge.lock` as Bin Wu; only the enumerated
maintenance paths are included. No item node, proof, statement, Lean module,
claim, live state or active sandbox is changed by this maintenance.

Provider recovery was installed by parallel maintenance, not authored here:
NK's `a1a68055f2` installs the retry supervisor and Q53's `6fb280508f` preserves
transport/reader handoffs; NC's `0abb765411` retains interrupted reader reports.
Q33's adaptive provider-capacity control was also being deployed during this
session. This patch preserves those changes instead of replacing the dispatcher
with an earlier snapshot.

## Validation and activation

The nine project-state regressions pass locally, as do the six existing compiler
failure-classification checks. Changed Python files parse. A read-only migration
preview identified the isolated N1 workers, including this item's still-running
PID, and excluded them from live-project N1. No API, SSH or Lean compiler is used
by these unit tests.

The running dispatcher keeps its loaded Python until its next normal start.
The source fix is installed for that start; the current service and worker are
left running under the user's prohibition on killing processes we did not start.
The item route note is available to the running dispatcher's next launch.

## Next worker

Resume the seven-step split and its 15 citation pairs in the existing sandbox.
Recheck any changes since the retained second-reader audit, run the prescribed
server dry run, and answer READY as the author. A fresh independent reader then
finishes its checks and delivers. Do not manufacture `.check` as an author.
Provider 429s require transport recovery, not a new mathematical split. Read the
new batch2 state file after migration; the shared legacy state is historical.
Failures are counted and never make the item ineligible.
