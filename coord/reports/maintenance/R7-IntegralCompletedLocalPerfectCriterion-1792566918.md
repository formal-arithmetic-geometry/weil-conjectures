# R7: missing completed-local-perfect artifacts

Incident: `Sheaf.Paper.IntegralCompletedLocalPerfectCriterion@new`, stage 3,
2026-10-21. Maintenance directory:
`/home/ubuntu/weil-launcher-all/maint/R7-Sheaf.Paper.IntegralCompletedLocalPerfectCriterion-1792566918`.

## Cause

This was a publication gap, not a mathematical failure. Landing
`20261021T061432-L-1774768`, commit
`461e0274ffc405dd25a5e3edd03e25a3da23f83d`, introduced both
`Sheaf.Paper.IntegralStratifiedPerfectModels` and
`Sheaf.Paper.IntegralCompletedLocalPerfectCriterion` at 06:14 UTC (14:14 +08).
The last published green build was `cc9c0f6fc42325e9acc8f9d18d91d6659cbbd8f3`
at 06:02:08 UTC. The landing record is still a request for global verification.

The dispatcher started the new item at 14:18:53 +08 while its direct public
import had no published `.olean`. All eleven completed attempts inspected
(run suffixes 1792563533 through 1792566285), and the subsequent 1792566925
attempt, reported that same missing artifact before elaboration. The six-count
maintenance trigger is not a retry cutoff. The coefficient probes succeeded;
there was no provider or SSH failure.

`tools/batch_land.py` explicitly lands deliveries without recompiling them.
`tools/remote_compile_set.py:72` resolves library imports from
`lean/.lake/build/lib/lean`; its explicit artifact overrides cover the worker's
own sandbox outputs, not another group's new landing. Thus a newly stated node
can be assigned while the compile service cannot load its statement dependency.
The worker publication rule forbids rebuilding landed dependencies in the
sandbox, so further identical attempts could not repair it.

The publication delay was prolonged by the scheduled upstream sync: the
build-loop log ended after the 14:05 green build and sync scheduling; the
upstream-sync log still reported the ongoing sync and a greater-than-one-hour
alert at 15:05. No such process was interrupted or modified.

## Repair

Compiled the two unchanged new modules, sequentially, using
`SHEAF_GROUP=MR7IntegralCompleted1792566918 tools/lean_file.sh lean/<module>.lean`.
The script retained its configured 60-second limit. Model compilation took
18.3 seconds; criterion compilation took 26.6 seconds. Outputs were written to
the new private maintenance mirror
`local/build/MR7IntegralCompleted1792566918/`.

Under `SHEAF_LEAD=L-only flock coord/.merge.lock`, checked each source SHA-256
against the reviewed landing and its git blob against the compiler's `.src`
record, and restored the six absent artifacts for each module under
`lean/.lake/build/lib/lean/Sheaf/Paper/`:
`.ilean`, `.ir`, `.ir.sig`, `.olean.server`, `.olean.private`, and `.olean`.
Each file was prepared completely and installed without overwriting an
existing path; each `.olean` was installed after its companions. Refreshed the
build-library directory timestamp so group mirrors can discover the additions.
The adjacent artifact JSON records source and output hashes and prior absence.

No Lean source, DAG node, claim, return, queue, dispatcher state, launcher-owned
file, review service, or landing tool was edited. Global build metadata and the
pending landing's verification state were preserved. These are incremental
artifact repairs, not a claim that a global build passed. Existing shared
artifacts were not replaced, so none required a `.bak`. All persisted additions
are new paths. The local worker report is backed up before adding the handoff.

## Validation

After restoration, the ordinary command

```
python3 /home/ubuntu/weil-launcher/lcompile.py /home/ubuntu/weil-sandbox/R7/Sheaf.Paper.IntegralCompletedLocalPerfectCriterion/lean/Sheaf/Paper/IntegralCompletedLocalPerfectCriterion.lean
```

compiled successfully in 21.8 seconds, exit code 0, using the published library
path. The item still has its original theorem hole. No mathematical proof was
attempted and no library hole was closed or introduced by maintenance.

## Protected pipeline follow-up

The durable correction belongs to the landing/artifact handoff: make the
already-checked artifacts of newly landed modules available to all worker
compiles through a source-hash-checked overlay (including every Lean module
companion and the required import closure). Reconcile that overlay with later
global publications and source restoration/quarantine. This allows immediate
dispatch without relying on the next global build. The existing `--setup`
artifact mechanism can carry these modules, but currently receives only the
request's sandbox artifacts.

The landing tools are explicitly protected by this maintenance assignment, so
they were inspected but not changed. No concurrency cap, throttle, admission
limit, dispatch suspension, or process termination was introduced. The
item-specific failure is repaired; this general handoff gap remains a tool-owner
follow-up.

## Next worker

Resume the preserved sandbox and the original theorem. The normal compiler can
now load `IntegralStratifiedPerfectModels`; do not copy or redeclare it. Retain
the coefficient-completeness/locality and uniform-profile probes already in
`scratchpad/`. Earlier report entries describe the historical artifact failure
and do not describe the repaired current environment. The initial delivery
check's `FAILED: nothing is proved` is accurate for the unchanged packet: finish
the assigned proof and deliver normally. Neither the proof obligation nor its
signature has changed.
