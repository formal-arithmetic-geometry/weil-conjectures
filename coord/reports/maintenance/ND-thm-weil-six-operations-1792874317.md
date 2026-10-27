# ND maintenance: thm-weil-six-operations (2026-10-25)

## Cause

Repeated completed Lean failures were caused by a source-reader/compiler version
mismatch, not provider errors or public/import-all visibility. The published
build is 54696378c79742b8b42dd2c10a62ac848ec9535c (2026-10-24T03:53:24Z).
Current Package.lean adds functorPackage and
exists_distTriang_rightDerivedLowerShriek_openClosed and changes the smooth
base-change field. Those mathematical changes have not been published.
tools/nt_source_overlay.py deliberately keeps changed interfaces on the last
green artifact; tests enforce that policy. Launcher scompile.py --source instead
reads the working-tree version, causing workers to assume unavailable names
should exist and repeat the same probes. Recent global builds are red; waiting
for publication cannot repair the worker's brief.

The item's recorded prop-functor-package attachment is only a compact-support
base-change comparison; the worker must repair that interface under §1(B) and
state the newest blueprint export. Maintenance has not done its mathematics.

## Repair

Added tools/nt_compile_source.py, a read-only compiler-aware source reader. It
uses the same private-source selector as both compilers; otherwise it reads the
published commit behind the artifact with git show, and reports provenance on
stderr. It refuses to substitute newer text if published source is unavailable.
Mathlib reads its package source. No artifacts or mathematical declarations change.

Added tools/test_nt_compile_source.py: regressions for changed interfaces, absent
artifacts, module-header conversions, unknown published commits, a new green
publication, Mathlib and invalid module names.

The launcher restores batch2/scompile.py through its integrity guard, observed
at 2026-10-25 04:49:00 in integrity/incidents.log. It is back to its original
contents. The durable launcher change is the item route note at
/home/ubuntu/weil-launcher-all/batch2/route-notes/thm-weil-six-operations.md,
which the dispatcher includes automatically in subsequent worker briefs. It gives
the read-only server-helper command and directs the worker to continue §1(A)/(B)
repairs using the actual available interface. No dispatcher/admission/review/
landing tool was changed, no process was stopped, and no limit was added.

## Validation

15 tests passed: python3 -m unittest discover -s tools -p 'test_nt*source*.py' -v.
The helper returns the old Package signature from the published commit, matching
the compiler. lean/.sandbox/maint-ND-six-operations/PackageBaseline.lean checks
the two available package declarations and the smooth-base-change field; compiled
using SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh in 4.8 seconds, exit 0. No lake build.
The same source was read through the launcher wrapper during its brief temporary
edit, then through the final helper directly after the guard restored the wrapper.

Backups: batch2/scompile.py.maint-ND-six-operations-1792874317.bak; item route-note
backup .maint-ND-1792874317.bak. Newly added server files have .bak copies alongside
them. Existing project files and DAG records were not edited.

## Next worker

Use the route note's tools/nt_compile_source.py command for compiler-selected
source, scompile.py for every worker compilation, and deliver2.py for delivery.
Re-read the newest blueprint and repair unusable dependency records in the
delivery. Do not re-run old unknown-constant probes, introduce unavailable
upstream names, or attach the full export to the finite-only theorem. A new green
publication may make the newer upstream declarations available automatically.

The launcher owner can eventually integrate the helper in scompile.py --source
and update its integrity baseline. That integration is optional for this item's
route and is documented in the maintenance REPORT.md.

## Commit record

The concurrent build snapshot already included both new tools in commit
2a87bbcc1c0ffcd7a7e40dfce9fe16e3cf9740ec before the maintenance commit acquired
the merge lock. Their working copies match that commit. This maintenance record
is committed separately under SHEAF_LEAD=L-only and coord/.merge.lock.
