# Q99 Frobenius local-term pipeline maintenance

Date: 2026-10-17. Item: thm-trf-frobenius-local-term, stage 1.
Local evidence and full report:
/home/ubuntu/weil-launcher-all/maint/Q99-thm-trf-frobenius-local-term-1792196921/.

## Cause

The first author run 1792190636 passed delivery preflight at 542964c37d and
returned READY. Reader run 1792193041 retained an independent reading and
several concrete citation repairs, but ended without last.txt. The following
six first-worker runs (1792195864, 1792195951, 1792196232, 1792196565,
1792196674, 1792196923) ended with Codex's fatal HTTP 429 diagnostic. The
dispatcher read only the missing last.txt and replaced the diagnostic with
NOANSWER. The reader role was also lost, so the item reverted to author work.
Some exits between reap and work were dropped before being counted; failure
counts are not an inventory of historical runs and remain dispatch-neutral.

The failures are infrastructure failures. There was no corresponding delivery,
return or landing entry for this item when inspected. Maintenance did not
change its statement, proof, unit realization or mathematical dependencies.

## Repairs verified

Other maintenance sessions deployed shared repairs during this investigation:

- a1a68055f2b73fe62674754cb95071667bd798ac adds the supervisor at
  tools/launcher/codex_retry.py, its fake-CLI tests and deployment guide.
  The installed /home/ubuntu/.local/bin/codex points to
  /home/ubuntu/weil-launcher-all/codex_retry.py. Future ordinary workers of
  the already running dispatcher use bounded jittered retries, resume a known
  session, and retain explicit provider diagnostics. The original entry point
  is backed up as /home/ubuntu/.local/bin/codex.maint-NK-1792196275.bak.
- 6fb280508f56f3ab9401bdc8651a572b0e6bee43 preserves the READY handoff by
  stage and delivery key and retains transport diagnostics in dispatcher
  source. 0abb765411 retains interrupted reader reports within a delivery
  round. These dispatcher source changes take effect at its next normal
  startup; this maintenance did not restart another session's process.

This maintenance adds tools/launcher/route-notes/thm-trf-frobenius-local-term.md
and this archive. The route note is installed at
/home/ubuntu/weil-launcher-nt/route-notes/thm-trf-frobenius-local-term.md, which
the running dispatcher reads when preparing a retry. It tells a mistakenly
restarted author to validate retained work and hand it to a reader, and records
the actual validation evidence without certifying the mathematical split.
Installation/commit uses SHEAF_LEAD=L-only and coord/.merge.lock, with identity
Bin Wu <844524296@qq.com>. Existing files are backed up before replacement;
new artifacts also have adjacent .maint-Q99-1792196921.bak snapshots.

## Validation and next worker

The exact Q99 CLI command shape is covered by the installed supervisor. Its
entry point and script hash are recorded in evidence/recovery-deployment.json
in the local report directory. On the server, 14 supervisor tests, 8 transport
and handoff tests, and 6 reader-retry tests passed. The local dispatcher source
was being edited concurrently by related maintenance sessions; only the
committed server test result is used as the reader-regression gate here.

Run 1792196953 passed server check_dag and review_split, then delivery preflight
at a267575343, 48393e480a and e2255ecee3, and returned READY. At 08:43:32 +08
the dispatcher started second-reader run 1792197812 through the deployed
supervisor; its codex-retry.json was present. No outcome is claimed in advance
for that reader. The sandbox has zero newly created nodes and zero new Mathlib
leaves according to the worker's READY response.

Resume the existing sandbox, honor the assigned author/reader role, repair
only concrete findings, then perform the current server dry run and delivery
as the brief requires. Citation excerpts can drift as other deliveries change
their source nodes. A past preflight success never replaces current validation.
No Lean compiler or Lake build was needed, and no process was signalled by
this maintenance.
