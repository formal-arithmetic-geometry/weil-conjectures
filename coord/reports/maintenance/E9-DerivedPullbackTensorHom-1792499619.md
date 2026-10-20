# E9 maintenance: DerivedPullbackTensorHom

2026-10-20. Item `Sheaf.Paper.DerivedPullbackTensorHom`, stage 3,
dispatcher key `Sheaf.Paper.DerivedPullbackTensorHom@510f3c176`.

## Result

The cause is diagnosed and independently reproduced. The operational fix belongs
in the explicitly protected dispatcher; it has **not** been applied. This is not
a mathematical failure, a permission problem, or a reason to retire the item.
The required launcher change is specified below, as instructed for protected
files. No failure-count cutoff or concurrency restriction is proposed.

## Cause and evidence

The original return is valid: delivery `510f3c1766` was based on `b6c70955a`,
and another landing changed the item before it could land. The server recorded
that conflict in `coord/returns/E9.md` and `~/cc1/autoland.log`.

The environment subsequently changed. Upstream-sync quarantine commit
`29b1c235f4` moved the item, its six missing source prerequisites, and
`Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses` out of `lean/` and into
`quarantine/`. All eight have rows in `coord/rework.tsv`. The item row says
`imports Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`.

The root's recorded compile error is a declaration-owner collision:
`Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology` tries to introduce
`CategoryTheory.ringedSiteZerothHypercohomology`, already loaded from
`WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology`.
This belongs to the upstream migration/rework route, not to E9's theorem proof.
The server queue lists `RhomGlobalSectionsOfUniverses` as a rework root with a
2208-module cluster; it does not list this E9 item as an ordinary proof item.
At inspection the root was claimed by **X2** (2026-10-20T12:20:20Z).

`tools/rework.py` documents the existing human-approved recovery contract:
restore the root against the current library, adapt only consumers forced by
its changes, and let normal rework restoration and green verification reconcile
the quarantine. `tools/queue.py:195` applies that contract to ordinary items.

The launcher bypasses that contract for old claims/returns. In
`/home/ubuntu/weil-launcher-all/dispatch_all.py:764`, the open-return loop uses
the retained E9 claim and return to enqueue an ordinary `repair` immediately.
It does not consult rework eligibility and does not attach `rework_brief`.
That brief is added only in the later claimed/never-delivered path near line
818. The pending-request path at lines 754-763 also replays stored work without
revalidating rework eligibility. The exact item continues to be launched with
the old instruction to take the current file from `lean/`, which is impossible
on the current quarantined baseline.

The live dispatch log confirms the loop independently of static code reading:
at 20:33:35 +08 the worker reported the missing source/object files; at 20:33:48
the same repair was launched again. It reported the same failure at 20:43:48
and was relaunched at 20:44:01. The latest prompt still contains the old return
and no rework instructions.

Earlier attempts also encountered provider HTTP 429 errors and empty answers.
Those are external provider failures, were not repaired here, and do not
explain the reproducible quarantine failure of the current attempts.

## Independent validation

1. Ran `deliver3.check_import_sources` directly, read-only, against the retained
   sandbox and `origin/sheaf-dag`, excluding `__probe.lean` just as the delivery
   tool does. It exited 1 before any compile or push, rejecting these six sources:
   `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`,
   `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`,
   `Sheaf.Paper.IntegralOperationsPreserveConstructible`,
   `Sheaf.Paper.IntegralOperationsScalarComparisons`,
   `Sheaf.Paper.SfIntegralConstructibleLinear`, and
   `Sheaf.Paper.SfRationalizationKaroubi`.
2. Created the server probe
   `lean/.sandbox/maintenance/E9-DerivedPullbackTensorHom-1792499619/MissingImport.lean`
   and its `.bak`. It contains only `module` and a public import of
   `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`. Compiled that one file
   with `SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh`. Exit 1 in **1.4 seconds**:
   the module's `.olean` does not exist. No theorem proof was involved.
3. Checked the actual last published green commit,
   `c558237871d420fe1864804c2a92d1d98d4599ad`, published at
   2026-10-20T12:26:03Z. Its tree contains the quarantined item and lacks both
   original item/root paths. A green publication after quarantine is therefore
   insufficient evidence that this repair can compile.

## Required protected-file correction

Owner: the launcher. File: `/home/ubuntu/weil-launcher-all/dispatch_all.py`.
This file is explicitly forbidden to maintenance by the task instruction, so
no patch to it was installed.

Apply the server's existing rework classification/eligibility to returned,
pending, and retained claimed work as well as fresh claims. A retained return
must not turn a quarantined cluster member into an ordinary proof task.
Resolve such work through the current server rework roots and their claims;
an eligible rework task needs the quarantine baseline and rework brief.
Preserve the old proof-return obligation and sandbox so the original repair
can resume against the restored sources. Revalidate a stored pending request
instead of replaying an obsolete ordinary-proof brief.

Verify these cases: this E9 return while its root is quarantined; an eligible
rework root; an ordinary non-quarantined return including a zero-sorry repair;
a pending request whose module is quarantined after it was queued; and the
same E9 return after restoration. Continue all other eligible dispatches.
Failure counts must never affect any of those decisions. This is correction
of task type and dependency validity, not a new throttle or retry policy.

Do not weaken `deliver3.py`'s source check, copy only selected `.olean` files,
restore the eight files around the rework mechanism, erase the return, or
reset failure counters: none addresses the routing defect.

## Files changed and commit status

New local file: this `REPORT.md`, with `REPORT.md.bak` retained.

New server files: the probe and its `.bak` above, plus the maintenance note
`coord/reports/maintenance/E9-DerivedPullbackTensorHom-1792499619.md` and its
`.bak`. No existing Lean source, DAG node, sandbox packet, return, claim,
dispatcher state, launcher code, landing tool, or provider setting was edited.

Server commit: **none**. Attempted the required identity and lock protocol with
`SHEAF_LEAD=L-only flock -w 45 coord/.merge.lock`, followed inside the lock by
staging only this maintenance note and
`git -c user.name="Bin Wu" -c user.email=844524296@qq.com commit --only ...`.
The lock acquisition timed out (exit 1); the inner staging/commit commands never
ran. The server maintenance note remains untracked and backed up. After the
lock owner resolves the deadlock below, it can be committed under the required
lock. There is no change commit to cite and no operational repair is claimed.

There is a separate confirmed lock deadlock preventing normal writes. Server
PID 548736 (`~/cc1/proof-imports-cycle.sh`) holds `coord/.merge.lock` on fd 8
and `local/tree.lock` on fd 9 while waiting for child PID 554371
(`tools/add_proof_imports.py --apply-plan ...`). The child inherits both fds
and blocks acquiring `local/tree.lock` again on a separate fd 3. Its wait
channel is `locks_lock_inode_wait`; `lslocks` shows the parent's tree lock and
the child's blocked request. It had persisted for over 20 minutes.
`buildloop.log` and `rework-autorestore.log` also record merge-lock timeouts.

The child reaches `tools/add_proof_imports.py:339`, where `write()` calls
`landing.tree_lock()` to record the already-written imports as a landing. The
outer script's lock acquisition encloses this call. The tool owner must remove
the duplicate tree-lock acquisition in the
proof-import cycle/landing lock contract. The relevant scripts are
`~/cc1/proof-imports-cycle.sh`, `tools/add_proof_imports.py` (`write`), and
`tools/landing.py` (`tree_lock`). Landing tools are protected by this task;
they were not edited. No process was signalled or killed, and no lock file was
replaced or bypassed.

## Next worker

Preserve `/home/ubuntu/weil-sandbox/E9/Sheaf.Paper.DerivedPullbackTensorHom`.
Its report claims seven of twelve original holes closed and one new
coefficient-linearity prerequisite; those are retained, unaccepted proofs,
not a fresh passing compilation against today's baseline. In particular its
claim that all modules compile predates the quarantine.

The current lower-level migration repair belongs to the assigned rework root,
not to an improvised proof of this item. When sources return through that
workflow, compare the retained item with the restored current source and the
returned head, preserve signatures and completed work, rerun the required dry
run, then compile changed Lean files one at a time within 60 seconds and finish
the original returned-delivery repair. Merely retrying the unchanged packet
cannot succeed while the source and object diagnostics above still hold.
