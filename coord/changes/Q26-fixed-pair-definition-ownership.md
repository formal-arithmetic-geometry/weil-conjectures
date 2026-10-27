# Q26 fixed-pair definition ownership maintenance

The L return on immutable head b7231942c778 requires a definition node owning
fixedPairShift, fixedPairTruncLE, fixedPairTruncGE and fixedPairCohomology, and a
Postnikov statement dependency on that owner. The worker prepared this extraction,
but batch2/deliver2.py discards the dependency node's stmt_deps. The stage-2 reader
also permits only lean changes on an existing dependency. Its preflight therefore
passes the incomplete packet, and the worker correctly declines to publish it.
Repeated dispatch cannot satisfy the return within those delivery field rules.

Maintenance installs the already prepared extraction as a shared library repair.
def-zl-fixed-pair-truncation-cohomology-functors owns the four existing functors in
FixedPairTruncationCohomologyFunctors. FixedPairPostnikovIdentifications publicly
imports that module, and its node cites the definition in stmt_deps. The Postnikov
lean record names only its own theorem. The four moved signatures and bodies and
the entire retained Postnikov proof are identical to the previous source. No item
mathematics or theorem statement is changed; no new sorry or axiom is introduced.

The two modules are installed together through tools/land_set.sh (group L), with
tools/lean_file.sh checking each file separately at the standard 60-second limit.
Definition metadata and the incremental graph checks also pass. Backups are under
local/maintenance/Q26-fixed-pair-1792879058/backups/<original path>.bak; an empty
backup plus .bak.absent denotes a previously absent file.

The retained Q26 sandbox should deliver only its item node, item module and report.
The definition and Postnikov extraction now belong to the base and must not be
redelivered from stale sandbox copies. Keep the direct definition citation,
proof-only theorem dependencies and direct IsTExact heart membership proof. The
normal worker dry-run and independent review remain required for the consumer.

No launcher, preflight, review, landing tool, admission or concurrency setting is
changed. A general tool repair would need an explicitly represented, authorized
definition-extraction delta, preserved consistently by deliver2.py, the stage-2
reader, preflight graph projection and landing. Silent field dropping must not be
reported as complete satisfaction of such a return. Those protected tool changes
are outside this maintenance assignment.
