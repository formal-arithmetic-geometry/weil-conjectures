# N8 maintenance: prop-sf-pf-coherence

2026-10-20. Stage 2; dispatcher key `prop-sf-pf-coherence@new`.

## Result

Fixed a maintenance-job deadlock that held the server merge lock and prevented
dependency repairs from landing. The repair is deployed, all three regression
tests pass, and ordinary landings have resumed. The automatic build captured the
code changes in `89421ca049a44e986f8a47898d484955b2974351` (Bin Wu,
844524296@qq.com); that commit was published green at **13:11:28 UTC**.

The item's quarantined dependencies still require restoration through the
existing rework pipeline. This report does **not** certify the saved statement
packet or claim that its dry run passes. No item mathematics was changed.

## Causes and evidence

There are distinct historical failures:

1. The earlier attempts followed an obsolete Q79 stage-1 handoff even though
   Q75 had already landed the split in `697b9ab6aa7cc1deb30740a051c1223faa5f6856`.
   Previous maintenance corrected that route note. The current worker brief
   correctly assigns stage 2 and the retained N8 sandbox.
2. Attempt `prop-sf-pf-coherence.1792447236` ended in provider HTTP 429 after
   sixteen provider recovery attempts. This external provider failure was not
   repaired here. Later attempts reproduce a different, local pipeline failure.
3. The current source/object failures follow upstream-sync quarantine commit
   `29b1c235f4`. `coord/rework.tsv` lists
   `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`,
   `Sheaf.Paper.SixFunctorDatum`, and
   `Sheaf.Paper.SixFunctorOperationDatumStages`. Their sources were moved from
   `lean/` to `quarantine/`; the prescribed source reader therefore reports
   unavailable. This is deliberate quarantine, not a missing definition to
   invent in the N8 packet.

The recorded root error is independently reproducible:

```
import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology failed,
environment already contains 'CategoryTheory.ringedSiteZerothHypercohomology'
from WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
```

Compiling the quarantined root with
`SHEAF_GROUP=maint-N8-1792501236 SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh`
failed on that collision in **3.8 seconds**. The retained import-only
`scratchpad/CurrentDatumImport.lean`, compiled through `scompile.py`, failed
before elaboration on missing `RhomGlobalSectionsOfUniverses.olean`; the
current-server confirmation failed identically in **1.1 seconds**.

X2 already delivered the import repair in
`68becc60fe7e7d4edf36fe4d653a7e24a46014ef`, branch
`deliver/X2/Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`. It restores
the existing proved root and makes the compatibility module re-export the
identical upstream hypercohomology definition. Its report records successful
compilation of both files and both direct consumers. The branch was still
pending in the normal landing queue at the last check; I did not duplicate or
bypass that delivery.

The reason repairs could not land was a separate maintenance-tool defect:

- `/home/ubuntu/cc1/proof-imports-cycle.sh` acquired `coord/.merge.lock` on
  descriptor 8 and `local/tree.lock` on descriptor 9.
- Its child, PID 554371, ran `tools/add_proof_imports.py --apply-plan ...`.
  After writing imports, `write()` called `landing.tree_lock()`, opening
  `local/tree.lock` again on descriptor 3 and blocking forever. Flock ownership
  follows the open file description, so this was a conflicting second lock.
- The wrapper, PID 548736, waited for that child while retaining both locks.
  `/proc/554371/wchan` was `locks_lock_inode_wait`; both processes' descriptor
  9 referred to tree-lock inode 2240278. The merge-lock inode was 658188.
  Kernel lock records named the already-exited flock helper PID 554343,
  explaining the misleading “command line unreadable” timeout messages.
- `~/cc1/autoland.log`, `buildloop.log`, and `rework-autorestore.log` repeatedly
  reported merge-lock timeouts. The deadlock had lasted over forty minutes.

The old child was terminated **externally** at 13:10:43 UTC, as recorded by
the wrapper log, before my guarded live-recovery command could act. I killed
no process and released no live lock. The deadlocked processes disappeared;
subsequent logs show green publication and resumed landings at 13:12 UTC.

## Changes and backups

On `/home/ubuntu/weil-conjectures-sheaf`:

- `tools/add_proof_imports.py`: the writer owns one tree lock around the entire
  mutation and landing-record operation, including its guard and source reads.
- `deployment/proof-imports-cycle.sh`: removes the caller's redundant tree
  lock; the caller continues to own the merge lock.
- `tools/test_proof_imports_locking.py`: tests the actual wrapper's application
  block with real flock operations in a temporary repository; also checks that
  the writer holds the tree lock during mutation and record creation.
- `tools/test_proof_imports_cli.py`: isolates its lock directory inside its
  temporary fixture.
- `tools/launcher/route-notes/prop-sf-pf-coherence.md`: adds the current
  quarantine diagnosis, existing X2 delivery, maintenance repair, and handoff.
- `coord/reports/maintenance/N8-prop-sf-pf-coherence-1792501236.md`: server copy
  of this maintenance report.

Also updated the deployed maintenance wrapper
`/home/ubuntu/cc1/proof-imports-cycle.sh`, preserving its existing deployment
differences, and the local worker route note
`/home/ubuntu/weil-launcher-all/batch2/route-notes/prop-sf-pf-coherence.md`.
Every pre-existing changed file has its original saved alongside it with suffix
`.maint-N8-1792501236.bak`. Local review copies and backups are in `repair/`.
The new test and report had no previous versions to preserve.

The four tracked code/test changes were captured by the build service in
`89421ca049a44e986f8a47898d484955b2974351`. The route-note/report follow-up is
committed separately under `coord/.merge.lock` with the required Bin Wu identity;
its hash is available in the report path's Git history.

No dispatcher state, failure count, item node, saved Lean module, review service,
or delivery/landing-tool implementation was edited. No concurrency restriction,
delay, admission rule, or dispatch pause was added. I ran no Lake/global build;
the existing build service published its own build.

## Validation

`python3 -m unittest discover -s tools -p 'test_proof_imports*.py' -v`:
**3 tests passed**. Both tracked/deployed shell wrappers pass `bash -n`, and
`git diff --check` passes. The regression tests use isolated files and actual
locks, without compiling Lean or touching the live library.

Live evidence after the deadlock cleared: the build published commit
`89421ca049` green in twenty seconds; `autoland.log` records multiple successful
landings at 13:12 UTC. Restoration of the quarantined dependency chain remains
a separate condition for the N8 packet to compile.

## Protected dispatcher follow-up

`/home/ubuntu/weil-launcher-all/dispatch_all.py` is explicitly protected by the
task, so it was read but not edited. Its pending-request replay at lines 754–763
reuses stored `extra` verbatim. Its claimed stage-2 readiness helper checks
whether dependency nodes have Lean records, which still exist for quarantined
modules; it reports no blockers for this item. Rework instructions are added
only in the stage-3 claimed-item path near line 819. Consequently the N8 prompt
repeatedly asks the worker to retry an unavailable published dependency without
the current quarantine/rework context.

Needed launcher change: refresh current quarantine/rework context in prompts
for pending, returned, and retained work, including the dependency modules of
stage-2 nodes. Include the current root repair's owner, delivery head, and
landing/verification status rather than replaying only an obsolete failure
note. Preserve dispatching and failure accounting; this is a briefing correction,
not a proposed pause or failure-count cutoff. The item route note now supplies
that context without editing the protected dispatcher.

## Next worker

Retain `/home/ubuntu/weil-newtargets-stage2-sandbox/N8/prop-sf-pf-coherence`.
The stage-1 split is complete. Check the current status of X2's root repair and
the affected rework modules; delivery alone does not publish dependencies.
`quarantine/` and `coord/rework.tsv` explain absent sources. Use the canonical
library declarations and the prescribed stage-2 compile/dry-run/delivery path.
Once compilation reaches the saved statements, address their actual diagnostics
under the stage-2 brief; this maintenance made no mathematical assessment of
that packet.
