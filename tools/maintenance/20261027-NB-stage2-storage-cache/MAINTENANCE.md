Maintenance: NB / lem-pur-condensed-compositor-realization, 2026-10-27.

The server root filesystem really filled: cc1/diskwatch.log records 100% at
04:50, 05:00 and 05:21 (server/local UTC+8). It had recovered to 27 GB free
when this investigation began. A stage-2 compiler cache failure recorded at
04:58:53 remained reusable for one hour: AdicCohomologyTorsionNormalForm,
key b4c93a254f07a3369d9bcee9d18b59961300b402, rc=1, error code 28,
"no space left on device", elapsed 5.0 seconds.

tools/nt_srv_compile.py treated every rc=1 without a missing-module diagnostic
as a final Lean error. Storage errors were persisted as .fail records and were
also marked FAILED_IN_DELIVERED, skipping infrastructure confirmation. The
launcher batch2/scompile.py cached every status except 124 for six hours and
supplied no validity callback to reject already stored storage failures.
The delivery's temporary declaration probe creates fresh request paths, so the
observed repeated dry runs reached the server and replayed the same server
failure; stable-path compiles could additionally replay the launcher cache.

Fixes:

- The server compiler ignores old ENOSPC/quota failure-cache entries, does not
  persist new storage failures, and returns existing infrastructure status 75
  with an infrastructure message. Deterministic Lean errors retain their cache.
- The installed launcher compiler rejects status 75/124 and storage diagnostics
  both when writing its cache and when reading preexisting results. The exact
  deployed change is scompile-storage.patch. test_scompile_storage.py exercises
  the installed /home/ubuntu/weil-launcher-all/batch2/scompile.py.
- The integrity guard's documented --accept operation registered only this
  launcher compiler. guard-registration.json records the installed/pristine
  SHA-256 and the single changed manifest entry.

Six regression tests pass. The server tests execute the real kcompile cache
flow with only the Lean invocation replaced, including an old stored disk
failure, one produced concurrently, a fresh failure, actual source diagnostics,
and OS storage exceptions. No Lean source, node statement/proof/record,
dispatcher state, landing/review tool, concurrency setting, or process was
changed by this maintenance. No cache flush or manual storage deletion was
needed. The unchanged dependency's formerly failing key subsequently contains
rc=0, elapsed 6.3 seconds; see server-storage-evidence.json.

Backups:

- Server tools/nt_srv_compile.py.bak-NB-storage-1793051560
- Launcher batch2/scompile.py.bak-NB-storage-1793051560
- Launcher integrity/manifest.json.bak-NB-storage-1793051560
- Launcher integrity/pristine/weil-launcher-all/batch2/scompile.py.bak-NB-storage-1793051560
- Original compiler copies remain in the maintenance workspace as .bak files.

Continue the existing H2 repair in
/home/ubuntu/weil-newtargets-stage2-sandbox/NB/lem-pur-condensed-compositor-realization.
It supplies def-pur-compact-support-realization-factorization with existing:true
ownership of rho/q/realizedFactorization/atNormalized/IsFactorized, and replaces
the unneeded theorem dependency. This maintenance changes none of that packet.
Use the normal scompile.py / deliver2.py workflow. There is no reason to alter
the mathematics to address a disk diagnostic. If storage fills again, it is an
infrastructure problem; these tools now let unchanged requests recover when
space is available. Operational disk pressure remains visible to the existing
diskwatch; this patch does not change that service.
