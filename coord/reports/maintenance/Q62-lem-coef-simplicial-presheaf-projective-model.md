# Q62 maintenance: `lem-coef-simplicial-presheaf-projective-model`

## Cause

The repeated failures were provider transport failures. All ten counted runs,
plus the maintenance relaunch observed as run eleven, ended with Codex's
terminal `ERROR: exceeded retry limit, last status: 429 Too Many Requests` and
no `last.txt`. The dispatcher therefore recorded only `NOANSWER: ` and started
fresh sessions. The same 429 wave affected many unrelated groups. The item is
already a reviewed stage-1 split; the server has no Q62 return, rejected
delivery, or item-record fault.

## Fix

The shared recovery fix was already installed by related maintenance, so I
verified it and did not overwrite it:

- `a1a68055f2b73fe62674754cb95071667bd798ac` installs
  `tools/launcher/codex_retry.py`, its tests, and documentation; new dispatcher
  workers use `/home/ubuntu/.local/bin/codex` pointing to the supervisor.
- `a5ae0952c31d887797156fd16ea7208a894cae05` supervises explicit dispatcher
  `exec resume` calls.
- `6fb280508f56f3ab9401bdc8651a572b0e6bee43` preserves worker handoffs and
  transport diagnostics in the dispatcher.
- This maintenance added the item handoff
  `tools/launcher/route-notes/lem-coef-simplicial-presheaf-projective-model.md`
  and the matching server maintenance report in commit
  `93af03cb3cbb9109da85ce61a28131388b91d5cc`.

No Lean source, node record, claim, failure counter, or unrelated server work
was changed. No process was killed.

## Validation

The installed retry supervisor passed its 15 fake-CLI regressions locally and
on the server, including startup 429 recovery, same-session resume, explicit
resume retry, bounded exhaustion, permanent-error exclusions, cancellation,
and real-answer precedence. `attempt-evidence.json` records every item run,
session ID, terminal request ID, and the installed wrapper hash.

The post-fix run `1792197037` retained a substantial sandbox module and reached
a genuine Lean type error. That is ordinary item work after the transport fix,
not a dispatcher failure.

## Next worker

Continue the retained sandbox at
`/home/ubuntu/weil-newtargets-stage2-sandbox/Q62/lem-coef-simplicial-presheaf-projective-model`.
If run `1792197037` finishes with `READY`, let the normal second reader and
stage-2 landing process continue. If it exits without an answer, inspect and
continue that sandbox; the next ordinary dispatch uses the recovery wrapper.
Compile individual Lean files only with the prescribed 60-second tool, never
`lake build`, and do not redo the mathematics from scratch.
