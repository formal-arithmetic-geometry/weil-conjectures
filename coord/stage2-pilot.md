# New-targets stage-2 pilot — 2026-10-15

Completed with ONE group, NA, two worker/second-reader slots and exactly two distinct
items. The bounded dispatcher (PID 1443208) is stopped. NA has no remaining claims,
delivery branches or running workers. The stage-1 dispatcher remains stopped by
STOP_STAGE1; start.py and dispatch.py respect that marker. No other group was started.
The separate s1fix session completed its work during the pilot; its nodes were not
edited by this stage-2 task. Final queue reports stage 1: 0 nodes to split.

## Changed files

Under ~/weil-launcher-nt:
- dispatch.py: explicit stage selection; stage-2 briefs; separate run/log/PID/lock;
  project/clone/sandbox parameters; stage-2 claim filtering; bounded item limit.
- deliver2.py, worker-brief2.md, check-brief2.md: ported from the first launcher;
  new-targets branches/tree, independent reader delivery, server-only compilation.
- scompile.py: sends each file to the side server's private compile overlay.
- start_stage2.py: starts the first N configured groups, two slots each by default.
- msearch.py: respects WEIL_SANDBOX without changing the stage-1 default.
- start.py and STOP_STAGE1: prevent the watchdog from reviving stage 1.
- README.md, STAGE2.md: operational documentation and historical stage-1 distinction.
Existing modified files and source versions of ported files have *.bak-stage2 backups.

Under the server's ~/weil-newtargets:
- tools/nt_compile.py, lean_file.sh: per-file compiler against live artifacts read-only,
  nice 19, two threads, hard 60 seconds for every file; private temporary outputs.
- tools/land.sh: side-only file landing and per-file checks, no global-build request.
- tools/stage2_delivery.py: recognizes the server compile backend without a side build.
- tools/preflight_delivery.py, merge_delivery.py: authorize stage 2; keep stage 3 disabled.
- tools/nt_merge2.py: commit identity and trailer for the existing --stage 2 merger.
- tools/nt_land2.py: side merge, then field-wise shared DAG promotion with conflict checks
  and a resumable journal; never copies a Lean file to live.
- tools/queue.py, nt_stage2.py: stage-1 priority, no stage-3 source scan, and conservative
  deferral of the pro-etale target family awaiting framework validation.
- tools/sync_newtargets.py: preserves stage-2 claims and uses the required commit policy.
  Only these hunks were committed; the s1fix session's pending hunks were left intact.
- coord/sheaf.env: stages 1,2 opened only after the compiler smoke test; pro-etale skips.
- coord/brief-stage2.md, STATE.md, stage2-pilot.md: side-specific rules and evidence.
The two module/node/report landings and queue/ledger bookkeeping are recorded below.
Backups of changed server files are *.bak-stage2.

## Delivery evidence

| Item | Delivery head | Side landing | Shared DAG landing | Final compile |
|---|---|---|---|---|
| def-weil-pbc-ind-etale-algebra | 98890e632c | 74d88eb379 | a76eea4912 | 1.2 s |
| sbc-def-coefficient-conventions | 56f5de543b | 5e4e7bb474 | 2557ec6cdb | 1.3 s |

Files: lean/Sheaf/RingTheory/IndPrincipalZariski.lean and
lean/Sheaf/AlgebraicGeometry/SmoothBaseChangeCoefficients.lean, on the side only.
Each passed worker dry run, independent second reading, maintainer source review,
side merger dry run and actual landing. Maintainer reviews and immutable delivery
snapshots are in evidence/delivery1 and evidence/delivery2; the reviews are also
server-side local/stage2/reviews/. The final two file checks used the current live
published library after the concurrent upstream sync. Neither module contains sorry.

The compile smoke test covered two sibling modules compiled separately; an
intentionally ill-typed file failed as expected. The pilot exposed and fixed a
Lean namespace-root shadowing issue in the private artifact overlay. Output links
are removed before compilation; live artifacts are never written through them.

## Landing and restart

Worker -> dry-run deliver2.py -> independent second reader -> deliver/<group>/<item>
on the side server -> maintainer reads immutable head -> nt_land2.py ->
merge_delivery.py --stage 2 under side coord/.merge.lock -> side lean/ and DAG/report
commit -> field-wise DAG-node delta under live coord/.merge.lock. A journal records
both commits. No live Lean, build request, configuration, claim or ledger is written.
All task commits use Bin Wu <844524296@qq.com>, SHEAF_LEAD=L-only and the requested
Claude Opus 5.5 trailer. Existing lock-taking merge tools are never wrapped in flock.

For N configured groups, after setting N to the desired count:

```bash
python3 ~/weil-launcher-nt/start_stage2.py "$N"
```

WEIL_SLOTS defaults to 2; project and clone prefix default to the new-targets paths.
The pilot-only --item-limit 2 is omitted for continuous claiming. This command was
NOT run for more than one group. Maintainer review/landing remains explicit; the
dispatcher does not auto-approve deliveries. See STAGE2.md for the landing command.

## Stage-3 boundary and concurrent work

Both task-owned live commits were audited and contain only their single intended
DAG JSON. Both new statement modules are absent from live lean/. No lake build or
global side build was run, no live build request created, and no live configuration
or library file was written by the task. The final live worktree audit was clean.
The live config hash did not change.

The whole live tree did change during this test: the independent upstream-sync
commit d1685a4695, launcher prover commits, s1fix DAG landings, queue updates and a
normal global-build commit are recorded in evidence/live-concurrent-history.txt.
The before/after manifest therefore is NOT an unchanged-tree claim. The two
stage-2 live commits themselves modify only the intended DAG files, as recorded
in evidence/live-landing-audit.txt and live-boundary-check.txt.

Residual resource cost is short nice-19 single-file compiles, temporary artifact
metadata and brief shared-DAG lock contention. Stage-2 modules are intentionally
not in the live library; a future live adoption needs a separate coordinated
landing. Pro-etale target-family nodes remain deferred pending framework validation;
the independent upstream sync was not modified by this task.
