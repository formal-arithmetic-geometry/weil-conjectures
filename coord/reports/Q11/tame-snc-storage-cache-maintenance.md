# Q11 tame SNC quotient compile-cache recovery

Item: lem-sfb-tame-snc-quotient-resolution, stage 2, dispatcher key
lem-sfb-tame-snc-quotient-resolution@new. Maintenance 2026-10-24.

The worker's repeated error 28 was infrastructure, not a Lean statement failure.
~/cc1/diskwatch.log records the root filesystem reaching 100% at 18:20 +08.
Earlier NR maintenance diagnosed generated local/nodes-cache growth and moved
that cache to /tmp/weil-sheaf-nodes-cache, preserving backups. Its recovery is
recorded in commit 4f0e76fffd455e0ae9dfabddda5bd4a345198325 and
coord/reports/NR/closed-row-ownership-maintenance.md. When Q11 maintenance began,
root had 43 GB free; later it had 67 GB free.

The remaining blocker was a poisoned negative compile-cache entry. In
tools/nt_srv_compile.py, INFRA_TEXT omits ENOSPC. kcompile therefore classifies
rc=1 plus "resource exhausted (error code: 28, no space left on device)" as final,
reuses the failure for 3600 seconds, and sets FAILED_IN_DELIVERED, suppressing
server confirmation. Repeated worker checks returned the cached 3.2-second
output even after disk recovery. This item's sandbox key was
43c06d5dff1e026c971f19341615b985c1bc8987, cached at 10:15:24 UTC.

At 10:57:36 UTC Q11 maintenance backed up and invalidated 32 ENOSPC-only .fail
records in ~/weil-nt-overlay/kcache/Sheaf.Stage2.Sandbox0. Each was rechecked
under its existing per-key exclusive flock; no active key was skipped. Each
original remains as <key>.fail.maintenance-Q11-1792839139.bak. The accompanying
JSON manifest records all paths and SHA-256 hashes. No successful artifact,
lock, source diagnostic, worker process or concurrency setting was changed.

Validation:

- The unchanged saved module passed the normal scompile.py check: sandbox 2.4 s,
  library 2.5 s. Key 43c06d5dff1e026c971f19341615b985c1bc8987 now holds rc=0.
- Normal deliver2.py Q11 lem-sfb-tame-snc-quotient-resolution --no-push passed
  preflight and compilation at dry-run commit 71e97e34034. Nothing was pushed.
- A separate tools/lean_file.sh invocation (60 seconds) on a private scratch
  copy found a missing published ClopenGeometricCategoricalQuotient.olean.
  The normal wrappers correctly prepare that landed-source dependency privately;
  they are the successful full-packet validation above. No global build ran.
- The saved Lean module and node were unchanged. The sandbox report was backed
  up as report.md.maintenance-Q11-1792839139.bak and given a recovery handoff.

Next worker: keep the packet, rerun the normal saved-packet dry run against
current sources, then complete the prescribed delivery and independent review.
Old error-28 retry notes precede this recovery. No mathematics was needed here.

Needed protected-tool change: make the infrastructure classifier recognize
ENOSPC / error code 28 / no space left on device, use that classifier both for
negative-cache reuse and FAILED_IN_DELIVERED, and never retain such failures as
final source diagnostics for an hour. Existing infrastructure failures must be
retryable after recovery; genuine Lean diagnostics should remain cacheable.
nt_srv_compile.py also produces landing compile receipts, so maintenance treated
it as covered by the user's protected landing-tool boundary and did not edit it.
The launcher/tool owner should make that code change. Cache-data invalidation
has restored the item without changing the protected implementation.
