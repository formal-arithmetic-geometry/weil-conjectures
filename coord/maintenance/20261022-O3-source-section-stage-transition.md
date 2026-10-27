# O3 maintenance: source-section stage handoff

The item `lem-trf-source-section-stalk-cone-comparison` repeatedly received an
obsolete stage-1 assignment. Its accepted mathematical split is intact. Maintenance
released the old O3 claim through `tools/claim.py release`; the current stage-2 row
remains available for normal dispatch. This is a release of completed stage-1 work,
not an abandonment of the stage-2 statement.

## Cause and evidence

- Q06's accepted split landed as `9546512f0f4` at `2026-10-22T09:45:32Z`,
  reviewed PASS by `NT-cc-Q06-b674ac0bf`. See `coord/ledger.md` and
  `coord/deliveries.log` at that time.
- O3 claimed the item at `09:45:50Z`, 18 seconds after that landing. The stale
  queue in the landing still listed stage 1. The claim contained no stage field.
- Queue commit `37cac849644` (`10:41:19Z`) removed the item. It did not reappear
  at stage 2 until `792c3e43141` (`16:03:57Z`). In the interval, `Group.server()`
  retained cached stage 1 when `claim.queue_stage()` returned no stage, and
  `Group.work()` relaunched the held claim without checking stage-1 completion.
- All 47 saved O3 attempts have stage-1 prompts and final unchanged-item
  rejections. The counter is 42 because the first five BLOCKED endings are
  accounted for separately. Runs are under
  `/home/ubuntu/weil-launcher-all/run/O3/lem-trf-source-section-stalk-cone-comparison.*`.
  The first run is `1792662351`, the last is `1792679979`.
- The unchanged-item preflight refusal was correct: the sandbox node is the
  accepted seven-step split. No released repair note, O3 return or O3 delivery
  branch reopened it. Recovered provider interruptions in some runs do not
  explain the repeated final rejection; maintenance changed no provider setting.
- At maintenance time, the live queue and dispatcher state both correctly said
  stage 2. `node_finished(item, "1")` was true, `node_finished(item, "2")` was
  false, and the item had no Lean record. All 13 statement dependencies had
  records or a Mathlib match. There was no O3 running/pending worker and no
  stage-2 sandbox packet. The old stage-1 claim was therefore safe to release.

## Change and validation

The old claim `coord/claims/lem-trf-source-section-stalk-cone-comparison.lock`
was backed up and released through the normal claim tool. Its journal append is
in `coord/deliveries.log`, which was backed up too. Adjacent backups end in
`.maint-O3-source-section-1792696390.bak`. This new incident record also has an
adjacent copy with that suffix.

The maintenance commit includes only the obsolete claim deletion and this
record. The active journal already had unrelated uncommitted entries; it is
left to normal bookkeeping rather than committing others' pending work.
The commit runs under `SHEAF_LEAD=L-only flock coord/.merge.lock`, as Bin Wu.

Validation: claim absent immediately after release; stage-2 row retained;
no repair/return/delivery was changed; node SHA-256 unchanged at
`bfb98a35cd45cbb108c088246b140d3f700072c783188d9bcc38b86d837b133a`.
The accepted node, its Lean dependencies, original sandbox, generated queue,
launcher code, review service and landing tools were not edited. No Lean file
changed and no compiler or global build was run. No process was stopped and no
dispatch restriction was added.

## Protected dispatcher follow-up

The user explicitly forbade maintenance edits to `dispatch_all.py`. Its owner
should reconcile a held stage-1 claim after a successful live read when the node
is stage-1 complete and there is no current stage-1 row, open return or released
stage-1 repair. Give a legitimate stage-2 assignment its stage-2 brief. Preserve
the human's listed-item grant rule, genuine repairs and unrestricted dispatch;
never use failure counts as a cutoff. A failed read is not completion evidence.

When a queued stage changes while a worker runs, reap its result using the
saved running record's `stage`, not the current assignment's stage, and discard
an inherited note from another stage. Add regression coverage for completion
between claim/start and for a stage transition before worker exit. No such code
change is claimed here.

## Next worker

This is stage-2 statement work. Preserve the accepted split at `9546512f0f4`
and read Q06's report at
`coord/reports/Q06/lem-trf-source-section-stalk-cone-comparison.md`.
The old O3 BLOCKED answers concern stage-1 `deliver.py` and are not a stage-2
blocker. Follow `coord/brief-stage2.md`, inspect current dependency declarations,
compile every Lean file separately within 60 seconds, and use `deliver2.py`
for the dry run and delivery. A new stage-1 split requires a released repair order.
