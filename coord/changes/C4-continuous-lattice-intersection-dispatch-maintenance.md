# C4 ContinuousLatticeIntersectionSplitData dispatch maintenance, 2026-10-17

The ten empty `NOANSWER` results for
`Sheaf.Paper.ContinuousLatticeIntersectionSplitData@new` were terminal provider
HTTP 429 failures. The worker logs from timestamps 1792192665 through 1792196894
all end with `ERROR: exceeded retry limit, last status: 429 Too Many Requests`;
they have no `last.txt`. This was an infrastructure retry loop, not ten
mathematical failures. Counters are retained and the item stays dispatchable.

A separate, substantive issue remains in the Lean proof. The B2 proof landed
in e84721f760, then upstream-sync repair aabb04015d replaced the target's proof
by `sorry` after `(kernel) deterministic timeout`. `coord/returns/B2.md` records
that return. The node's old completed-proof provenance had not reflected it.
This maintenance updates the provenance notes while keeping the historical
review result and every mathematical field intact.

The first C4 worker (1792186488) returned READY after a dry run. Its second
reader (1792187310) did not push: the required current dry runs exceeded 60 s.
The dispatcher's `is_compile_limit` incorrectly rejected that exact diagnosis
because its infrastructure exclusion matched the word `push` inside
`--no-push` and `no delivery pushed`. It therefore suppressed the required
definition-repair guidance.

Changes on the worker machine:

- `/home/ubuntu/weil-launcher-all/dispatch_all.py`: ignore those negative push
  phrases when deciding whether a timeout is an actual push/transport failure.
  Actual worktree, compile-slot, SSH and push failures retain their handling.
- `test_dispatch_failure_classification.py`: the exact C4 diagnostic and a
  real reaper regression check the repair note, incremented counter and absence
  of a give-up state.
- `test_worker_transport.py`: supply the new stage-1 handoff dependency to its
  existing isolated dispatcher fixture.
- `/home/ubuntu/weil-launcher/route-notes/Sheaf.Paper.ContinuousLatticeIntersectionSplitData.md`:
  persistent handoff with the historical return, preserved sandbox and the
  isolated adjoint-isomorphism conversion. The dispatcher's existing launch path
  appends this note to the next author/repair prompt without restarting anything.

All three changed existing launcher files have sibling
`.C4-ContinuousLatticeIntersectionSplitData.bak` copies. The exact patch for this
maintenance, excluding other concurrent maintainers' changes, is recorded in
`coord/changes/C4-continuous-lattice-intersection-dispatch-maintenance.patch`.
The server node has a sibling `.C4-ContinuousLatticeIntersectionSplitData.bak`.

Validation: 33 targeted dispatcher, reaper, reader-recovery, provider-admission
and transport tests passed. Existing concurrent maintenance had installed the
`codex_retry.py` wrapper behind the CLI, with provider admission and retained
session/sandbox recovery; this maintenance checked its installation and tests
and did not replace it. The live dispatcher process predates the source fix;
the classifier source takes effect on its next normal restart. The route note
supplies the item-specific guidance to that existing process now. No existing
process was signalled or stopped by this maintenance.

The target's statement and Lean files are unchanged. The theorem remains an
open stage-3 performance repair. Current full-proof snapshots still exceed the
compile limit; historical successful compiles/axiom checks are not a current
delivery. The next worker should retain and diagnose the existing proof,
repair the expensive definition/conversion with its API and forced callers,
then pass the normal 60-second single-file check and dry run before a fresh
second reading. Rebase the node from sheaf-dag before updating its proof fields.

A further server-side check used `SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh` on
an isolated snapshot of the retained full proof, SHA-256
`29fb61fe072982c39a4a04b50b7f17ca9e7b23ad5712491527941b8f9932f4c2`.
It returned `Timeout after 60 s: the cause is a definition the file uses; find
it and change it.` No Lean file was modified or landed by maintenance. The
node keeps its original one-space JSON indentation; only its two provenance
notes differ from the pre-maintenance record.
