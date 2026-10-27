# O1 smooth-chart comparison: storage-cache recovery

Item: `lem-sfb-stack-smooth-chart-comparison`, stage 2, 2026-10-24.

The retained packet now passes the normal `deliver2.py --no-push` compile and
preflight: dry-run commit `33e24d96cf8`. No mathematical change was needed.

The original server failure was storage exhaustion. `~/cc1/diskwatch.log` records
`/` at 100% at 18:20 +08. Earlier NR maintenance identified generated
`local/nodes-cache` growth and moved it to `/tmp/weil-sheaf-nodes-cache`; its
recovery record is `coord/reports/NR/closed-row-ownership-maintenance.md`, commit
`4f0e76fffd455e0ae9dfabddda5bd4a345198325`. That recovery predates this work.
At this investigation the server had 88–92 GB free on `/`, with free inodes.

Continued retries replayed a negative compiler-cache result rather than running
Lean. Instrumenting `nt_srv_compile.key_of` without launching Lean identified
the exact item sandbox key `46b1e8968251fa82b6cef9af59b67ac113212df1`.
Its rc=1 ENOSPC result was recorded at Unix timestamp `1792837646.69598`
(2026-10-24 10:27:26 UTC), and every retry reused its `[13.7 s]` output.
The tool's `INFRA_TEXT` omits storage failures; it caches them as final source
errors for an hour and sets `FAILED_IN_DELIVERED`, suppressing confirmation.
Both deliver2.py and standalone scompile.py therefore replayed the same result.

O1 backed up and invalidated 25 negative records containing exactly the storage
diagnostic `no space left on device`, across the compiler cache. Each was
re-read under its existing per-key nonblocking exclusive flock. Original bytes
were backed up, their SHA-256 verified, and only the failed record was removed.
No active key was encountered. Existing successful artifacts and non-storage
failures were preserved. Exact paths, contents and hashes accompany this record
in `stack-smooth-chart-storage-cache-maintenance.json`. Backup suffix:
`.maintenance-O1-1792839919.bak`.

The item's original failure backup has SHA-256
`f3198e58d5e4940f4cffbcc6477c9732778852bc501b1e96cec5759d0a6e8309`.
The same key now has rc=0, `[10.0 s]`, timestamp `1792840348.2155902`.
The unchanged two-module packet passes normal compilation and preflight.
A separate `tools/lean_file.sh` invocation with `SHEAF_FILE_TIMEOUT=60` on an
unchanged private copy exited in 0.3 s because the published build has no
SpaceSmoothLocalSourceTarget.olean (the other module of this delivery). The
normal delivery compiler supplies that dependency privately and passed.
No global build ran.

New server report paths have adjacent empty `.bak` files marking their prior
absence. The private verification copy is under
`lean/.sandbox/maintenance-O1-1792839919/`, also with an empty adjacent `.bak`.
The local launcher route note records the recovery for future retry prompts.
Source Lean modules, node records, dispatcher state and failure counts were
not changed by maintenance. No process was killed or admission setting changed.

## Next worker

Retain the packet and begin with its prescribed `deliver2.py --no-push` against
current sources, then finish ordinary delivery and independent review. Old
BLOCKED notes describe the pre-recovery state. Do not rewrite the mathematics
because of the historical ENOSPC message. Maintenance did not push the packet.

## Protected-tool owner follow-up

`tools/nt_srv_compile.py` also produces landing receipts through `compile_plan`;
its implementation was left unchanged under the task's landing-tool restriction.
The owner should classify ENOSPC/error code 28/no-space diagnostics as
infrastructure both in negative-cache reuse and in `FAILED_IN_DELIVERED`.
Old cached storage failures must not remain final source errors after storage
recovers. Preserve caching of real Lean diagnostics; verify cached ENOSPC followed
by successful compilation and an ordinary Lean error that remains cacheable.
No launcher, review-service or landing-tool implementation was edited.
