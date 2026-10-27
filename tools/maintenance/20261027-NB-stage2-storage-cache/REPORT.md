Fixed the repeated infrastructure failure for
`lem-pur-condensed-compositor-realization` (NB, stage 2).

The server really exhausted its root filesystem: its existing diskwatch records
100% usage at 04:50, 05:00 and 05:21 on 2026-10-27 (UTC+8). However, it already
had 27 GB free when maintenance began. The continuing failure was stale compiler
state, not evidence of a defective statement or proof plan. At 04:58:53 the
stage-2 server compiler cached rc=1, `resource exhausted (error code: 28, no
space left on device)`, for `Sheaf.Paper.AdicCohomologyTorsionNormalForm`, key
`b4c93a254f07a3369d9bcee9d18b59961300b402`. Every later dry run replayed that
5.0-second diagnostic because `tools/nt_srv_compile.py` classified it as a
deterministic Lean error, reusable for one hour. The launcher compiler also
allowed six-hour reuse of storage failures for requests with stable paths.

The origin of the disk pressure is also recorded in the server history. A
separate repair, `8e38f4daaacb8c23829b14224794b3850394fa81` at 05:52:58,
replaced a shared 1.4 GB pickle cache with keyed SQLite storage. Its commit
message explicitly records that rewriting the entire pickle at process exit
filled the disk twice that day. That repair predates this maintenance's code
changes; it explains why storage had recovered while this item's cached
failure persisted. The evidence is saved in `storage-origin.txt`.

Changes are committed on the Weil server in
`0083762c610ad0304fb65722f5a69b636655439f`, using the required merge lock and
Bin Wu identity:

- `/home/ubuntu/weil-conjectures-sheaf/tools/nt_srv_compile.py`: ignore stored
  disk/quota failures, avoid persisting new ones, and report them using the
  existing infrastructure status 75 instead of blaming the Lean delivery.
- `/home/ubuntu/weil-conjectures-sheaf/tools/test_nt_srv_compile_storage.py`:
  four regression tests for recovery from stored/concurrent failures, fresh
  storage failures, preserved caching of real Lean errors, and infrastructure
  receipts for compiler/OS storage failures.
- `/home/ubuntu/weil-launcher-all/batch2/scompile.py`: reject storage errors and
  statuses 75/124 when storing results and when validating old cache hits. Its
  deployed patch and two regression tests are archived in the server commit.
- Server audit material is under
  `/home/ubuntu/weil-conjectures-sheaf/tools/maintenance/20261027-NB-stage2-storage-cache/`.

The integrity guard restored the first launcher edit during testing. I used its
documented `check.py --accept` maintenance operation for exactly
`batch2/scompile.py`; only that manifest entry changed. Installed and pristine
copies both have SHA-256
`25f63cfc42d3328ad69363d675ca64d453e2be2fe613fbc9b78fee367427120c`.
`guard-registration.json` records this verification.

All existing files changed have backups:

- Server `tools/nt_srv_compile.py.bak-NB-storage-1793051560`.
- Launcher `batch2/scompile.py.bak-NB-storage-1793051560`.
- Launcher `integrity/manifest.json.bak-NB-storage-1793051560`.
- Launcher `integrity/pristine/weil-launcher-all/batch2/scompile.py.bak-NB-storage-1793051560`.
- Original compiler copies also remain in this working directory as `.bak` files.

All six regression tests pass. On the actual server, the exact formerly failing
dependency key has now compiled successfully, rc=0, in 6.3 seconds, replacing
the cached disk failure. Evidence is in `server-storage-evidence.json` and the
regression logs. A normal `deliver2.py NB
lem-pur-condensed-compositor-realization --no-push` completed with exit 0:
`OK (dry run): commit e4004092ccf passes the preflight and compiles; nothing pushed`.
The complete saved H2 packet is therefore validated. See
`validation-dry-run.log` and `validation-result.json`.

The next worker should retain the complete sandbox at
`/home/ubuntu/weil-newtargets-stage2-sandbox/NB/lem-pur-condensed-compositor-realization`.
The existing H2 repair registers the five plain definitions through
`def-pur-compact-support-realization-factorization` with `existing:true` and
replaces the unneeded theorem dependency. It was not changed by maintenance.
Its prescribed dry run now passes. Finish the worker's normal self-check and
deliver with `python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py NB
lem-pur-condensed-compositor-realization`. Maintenance did not push the item.
No cache reset, source edit to evade a cache key, or new mathematical work is
needed for error 28.

The server still has significant disk pressure (95% at the last inspection),
which its existing diskwatch tracks. This repair makes unchanged requests
recover after storage becomes available. No storage service, dispatcher state,
prohibited launcher script, landing/review tool, concurrency setting, Lean source,
node record, or other process was changed. Nothing was deleted manually.
