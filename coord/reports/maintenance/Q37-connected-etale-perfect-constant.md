# Q37 maintenance: lem-sfb-connected-etale-perfect-constant

The repeated empty NOANSWER results were provider HTTP 429 failures hidden by
final-answer-only reporting. The prepared stage-2 packet now passes compilation
and server preflight; the dispatcher has started its independent second reader.
Maintenance did not rewrite the mathematics.

## Cause and evidence

attempt-evidence.json inventories runs, terminal errors, answers, dry-run results
and log hashes. Eleven completed runs, suffixes 1792194131 through 1792196743,
end with “exceeded retry limit, last status: 429 Too Many Requests” and have no
last.txt. Several failed at startup. The prompt's count of ten is dispatcher
bookkeeping, not ten mathematical rejections. The old running dispatcher loses
these diagnostics and starts fresh author sessions, repeating reading and
packaging against the preserved sandbox.

There was also an early preflight error: lean.statement included the trailing
:=, which the signature parser excludes. The author repaired it while
continuing the work. Old and current constant-sheaf spellings were successive
worker versions, not evidence of a broken theorem or sync rule. At maintenance
time the current record already matched after whitespace normalization.
Maintenance canonicalized that whitespace only; it did not cause the 429 exits.

Server commit 48e573c8a0 is Q12's reviewed stage-1 split, with no Lean file or
lean record. It is not a stage-2 completion. Stage-2 dispatch is legitimate.
There is no item return in coord/returns/Q37.md, no stage-2 landing for this item
in coord/deliveries.log, and no corresponding landing failure in the inspected
~/cc1/*.log files.

## Fixes and paths

Shared fixes were installed concurrently by other maintenance runs:

- a1a68055f2: worker supervisor with same-session recovery and paced retries
  within the original deadline; later commits add provider admission and saved
  session fallback. /home/ubuntu/.local/bin/codex points to the installed
  /home/ubuntu/weil-launcher-all/codex_retry.py, so new workers of the already
  running dispatcher use it without a restart.
- 6fb280508f and 0abb765411: preserve transport diagnostics and independent-reader
  role/report. Dispatcher source edits take effect at its next normal start;
  they are not falsely claimed to be loaded in the old process.
- ecbefbec53: shared capacity accounting, including pending reservations.
  The installed supervisor's admission gate already manages new workers.

This maintenance adds tools/launcher/route-notes/lem-sfb-connected-etale-perfect-constant.md
on the server, deployed under /home/ubuntu/weil-launcher-nt/route-notes/ for
future author prompts. It identifies the prepared packet and preserves normal
independent review. This report and evidence are committed under
coord/reports/maintenance/Q37-connected-etale-perfect-constant*.

Validation found a server/deployed source mismatch in tools/launcher/codex_retry.py:
the server resume_session lacked the already-deployed guard requiring the stdin
- suffix and excluding --last. Its existing regression failed for an explicit
UUID combined with --last. Concurrent maintenance commits 8846ae9192 and
7aa72985b8 restored those guards before this maintenance attempted to patch it;
the patch refused the changed baseline and overwrote nothing. The final server
suite passes. No tool source was changed by this maintenance.

Local sandbox change:
/home/ubuntu/weil-newtargets-stage2-sandbox/Q37/lem-sfb-connected-etale-perfect-constant/dag/nodes/sec-six-functors-basics/lem-sfb-connected-etale-perfect-constant.json:
only lean.statement whitespace was canonicalized with the existing signature
reader. Backup: the same path plus .bak-maint-Q37-signature-1792197034.
No Lean source was edited by maintenance.

A temporary diagnostic note was written to dispatcher state during investigation;
the dispatcher subsequently replaced it with its own state. The final state
contains no maintenance override; failure counts were not reset or capped.
The observed state is preserved at
/home/ubuntu/weil-launcher-all/run/Q37/state.json.maint-Q37-observed-1792197034.bak.
The initial draft of this report is preserved as REPORT.md.bak; this diagnosis
supersedes that draft.

## Validation and outcome

- The prescribed scompile.py Q37 single-file check passed sandbox and library
  contexts, about three seconds each, without diagnostics. No global build ran.
- Author run 1792197037 passed deliver2.py --no-push at 0e43d6ee1f: compilation
  and server preflight pass, with only the expected second-reading section
  outstanding. It answered READY normally.
- The dispatcher started run 1792198028 as kind check. Its codex-retry.json
  confirms the installed supervisor is managing admission with the prepared
  sandbox retained.
- The actual eleven 429 logs are recognized by both installed classifiers.
  Supervisor, transport, reader-handoff and capacity regressions check recovery
  without API calls: 14 supervisor tests, 8 transport tests, 9 reader-handoff
  tests and 8 capacity tests passed (39 total). The server commit follows below.

No worker or dispatcher owned by another session was killed. No claim was
released or final-answer file fabricated. Another process's work was not landed
by maintenance.

## Next worker

Continue the retained packet and independent reading. Revalidate any edits with
the prescribed single-file compiler and deliver2.py. Only the independent second
reader pushes. Keep arbitrary Noetherian coefficients and every existing clause;
a provider failure does not justify changing the statement, restarting its
mathematics, or restoring an obsolete backup. The author's successful dry run
does not mean stage 2 has landed.

The maintenance report, attempt evidence and route note are the only server
paths in this maintenance commit. The commit uses Bin Wu <844524296@qq.com>
with SHEAF_LEAD=L-only while holding coord/.merge.lock. Server Git history
records the exact commit; its hash is appended to the local report after commit.
