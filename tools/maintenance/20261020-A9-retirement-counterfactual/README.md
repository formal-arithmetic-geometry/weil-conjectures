# A9 retirement counterfactual repair (2026-10-20)

Item: `Sheaf.AlgebraicGeometry.EtaleFieldGsets`, stage 3, group A9,
dispatcher key `Sheaf.AlgebraicGeometry.EtaleFieldGsets@new`.

## Cause

The worker was carrying the correct human-authorized RETIRE packet: replace all
14 direct consumer imports by the upstream twin, register its two instances,
move the existing DAG attachment, and list the obsolete module in `deleted.txt`.
The worker-side `deliver3.py:forced_adaptations` received no deletion manifest.
It compiled original consumers against the published baseline plus the changed
consumer artifacts, where the obsolete module still existed. OrbitCoproduct
therefore compiled unchanged and the tool rejected its migration as "not forced".
Removing the migration instead failed the same tool's deleted-import check.
Repeated attempts could not fix this contradictory delivery gate.

The initial historical attempt also had a zero-hole cleanup rejected as "nothing
is proved"; it preceded the complete retirement packet. The repeated current
failure was the deletion-unaware counterfactual, not a proof failure or a provider
error. There is no current A9 return or retirement landing in the server records;
the older EtaleFieldGsets landing in `coord/deliveries.log` and `~/cc1/autoland.log`
is the original October 12 proof, not this retirement.

## Deployed fix

`/home/ubuntu/weil-launcher/deliver3.py` passes the validated deletion list to
`forced_adaptations`. When an original directly imports a withdrawn module and
the delivered consumer no longer imports any withdrawn module, the report
records that the migration is required by the transaction. It explicitly asks
CODEX to check every accompanying API adaptation. Other changes retain the
original counterfactual checks, baseline-failure guard, and inconclusive-error
rejections. Existing claim, signature, preflight, and independent review checks
are untouched. The complete delivered set must still compile first.

A concurrent owner had added a retirement/rework zero-hole repair exception
while this investigation ran. That change was preserved. `deliver3.py.bak` is
the exact deployed base after that concurrent fix; `deliver3.patch` contains only
this maintenance patch. The tested deployed snapshot is `deliver3.py`, SHA-256
`9d279b4e971d0207926bfa01aaab7f9418c42fa9f9d6d98f8472e577d8282aff`.

The integrity guard accepted the deployment through its normal record/save
operation while holding its `.lock`. Backups with suffix
`.A9-retirement-1792503000.bak` exist for the deployed script, the integrity
manifest, and its pristine script copy. The guard itself was not changed.

## Validation

- Nine regression tests pass against both the candidate and deployed source.
  They cover the deletion handoff, retained/mismatched withdrawn imports,
  unrelated changes, real dependency errors, broken baselines, timeouts, and
  missing-artifact failures.
- Running the actual helper on all retained sources with every consumer treated
  as held by another group recognizes all 14 required migrations without a stale
  baseline compile. The other two sources are unchanged intermediaries.
- `packet-source-audit.json` confirms no consumer declaration, signature, body,
  or visibility changed and there are zero sorry tokens.
- The server's unchanged static preflight accepts the isolated transaction:
  `preflight OK (stage 3)`, review class CODEX. Compilation was disabled only in
  this static invocation and performed separately with the required wrapper.
- All 16 packet sources compile individually in import order through
  `tools/lean_file.sh`, with `SHEAF_FILE_TIMEOUT=60`, zero diagnostics, and maximum
  measured time 9.9 seconds. A unique group mirror holds the outputs.
- The real original OrbitCoproduct compiles against the published baseline
  (2.8 s). After compiling the actual empty withdrawal module in the private
  mirror, the original fails with `Unknown identifier Group` (1.3 s), while the
  adapted consumer succeeds (3.3 s). No fabricated compiler artifacts were used.

The detached packet validation commit is
`ddac9f1b27ab66bf60d2ad33a0484a713c7118fc`, based on
`e0d550965f59d281b6857b001e85491fc81c968b`. It was created with the requested
Bin Wu identity and `SHEAF_LEAD=L-only` under the main project's
`coord/.merge.lock`. It remains only in
`/home/ubuntu/weil-maint-A9-retirement-1792503000/preflight-worktree`; it was not
merged or pushed as an A9 delivery. Existing files changed in this isolated replay
also have `.bak` copies. The main library and worker sandbox were not edited.

An additional run of the existing, untouched
`python3 -m unittest discover -s tools -p test_forced_adaptations.py -v` has three
pre-existing failures: `test_evidence_and_own_interface_required`,
`test_signature_remove_public_add_visibility_rejected`, and
`test_never_auto_even_claimed`. The first two use unclaimed fixtures despite the
current unclaimed-module exception; the third expects CODEX for its fixture while
the current classifier returns AUTO. These protected policy tools/tests need an
owner's separate audit. This actual retirement remains CODEX and passes the
unchanged preflight. No protected landing/review tool was edited.

## Next worker

Keep the retained 16-file packet and `deleted.txt`; do not remove OrbitCoproduct
or DiscreteContinuousRepToCommGrp from the migration to appease the former gate.
The existing two unchanged intermediary files refresh transitive artifacts.
Refresh the historical BLOCKED paragraphs in the worker report after a successful
normal dry run, then use the usual delivery command. A process that loaded the
old delivery script must rerun the command in a fresh process. Independent CODEX
review and normal landing remain required. This maintenance did not push a
delivery, alter claims/dispatcher state, pause dispatch, add any limit, or restart
or kill another process. No protected launcher, review, or landing source needs
changing to clear this item.
