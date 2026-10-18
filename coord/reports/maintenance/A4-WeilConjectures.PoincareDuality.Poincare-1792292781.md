# Maintenance report: WeilConjectures.PoincareDuality.Poincare

Date: 2026-10-18. Group A4, stage 3, dispatcher key
`WeilConjectures.PoincareDuality.Poincare@new`.

## Outcome and cause

The current blocker is a defect in the protected landing gate, not unfinished
mathematics. The operational fix is specified and tested below, but **was not
installed**: the maintenance request expressly forbids editing "the review
service and the landing tools" and directs that their needed changes be described
in REPORT.md. `tools/stage3_gate.py` is used by preflight and the landing path.

At server commit `10527ea0b0fafb0d969cc7470c18096f1e908ded`,
`tools/stage3_gate.py:124` checks non-theorem body changes without consulting the
module's `ok` exception set. This contradicts the documented exception policy in
the same file. Its statement-change, added-declaration, and public-import checks
already consult that set.

The retained repair corrects the missing coefficient-invertibility hypothesis of
`boundedConstructible_tateTwistDerived`. Its wrapper must pass that proof, and
`poincareMap` and `cupProduct` use the named projection interface introduced by
the repair. These three required body changes are the **only** current gate
refusal. All three full declaration names are already explicitly authorized in
`coord/upstream-statement-exceptions.tsv:75` onward, added by the previous
maintenance commit `49110a30966fc1646fe0cf316138331f24bc08e0`.

The current delivery removes no declarations and changes no public imports.
Adding more registry entries or changing the Lean to evade the body check would
not fix this cause.

## Evidence and validation

- Dispatcher `run/A4/state-batch1.json` recorded ten tries and the same body-check
  diagnostic. `dispatch.log:145720` records the last completed attempt;
  `dispatch.log:145726` starts this maintenance task. Dispatching continued.
- Attempt `run/A4/WeilConjectures.PoincareDuality.Poincare.1792292509/log.txt`
  reaches preflight after the delivery tool's compile/probe phase and ends with
  exactly one reason: the three non-sorry definition bodies. The retained report
  records eight compiling modules and zero remaining sorries. The preflight's
  deferred/not-run compile labels are separate from the earlier delivery-tool
  compilation; they are not compiler errors.
- Earlier attempts also reported launcher-generated dirty tools. Inspection of
  the current `deliver3.py` shows the former post-commit tool rewrites have been
  removed. The last completed attempt does not report dirty tools, so that
  historical problem is not the remaining blocker.
- Server `coord/repair-notes/WeilConjectures.PoincareDuality.Poincare.json` and
  `~/cc1/autoland.log:12727` explain an earlier B3 timeout at 96 seconds. This is
  distinct from the current static gate refusal; no timeout increase is needed.
- I independently parsed the **actual eight sandbox modules** against the
  current server HEAD using `stage3_delivery.diff_module`, then called the
  unmodified `stage3_gate.gate`: `REFUSE`, with precisely those three bodies.
  The diff scanner counts one old sorried declaration and zero new ones.
- I executed the proposed one-line gate change **in memory only** against that
  same diff: `AUTO`, with no reasons. Four negative controls still return
  `REFUSE`: an unlisted definition body change, an unlisted theorem signature
  change, an attribute change on an exception-listed declaration, and adding
  `sorry` to an already proved exception-listed declaration.
- This isolated gate reproduction omitted the cycle check and is not a fresh
  full preflight, Lean compile, axiom audit, or permission to land. No Lean source
  changed in this maintenance pass, so no new compilation was necessary.

The full reproduction transcript is `gate-reproduction.txt` beside this report.
The server gate and local shared-repository copy have the same SHA-256:
`c4284176afe94e4d4f61940c4dbb8de6625d364f462bd966df9ba8d7358788c8`.
The server gate's hash was unchanged after the in-memory experiment.

## Required change for the landing-tool owner

Apply this narrowly scoped change to the authoritative project landing gate,
`/home/ubuntu/weil-conjectures-sheaf/tools/stage3_gate.py`, and refresh the shared
repository through its normal path. Do not add another temporary tool rewrite to
`deliver3.py`.

```diff
@@
-        data = [k for k in d["body_changed"] if d["old"][k]["kw"] not in ("theorem", "lemma")
+        data = [k for k in d["body_changed"] if k not in ok and d["old"][k]["kw"] not in ("theorem", "lemma")
                 and not s3.only_sorry(d["old"][k]["body"])
                 and not s3.fills_only_sorries(d["old"][k]["body"], d["new"][k]["body"])]
```

Update the adjacent comment to describe the explicit-exception case and add the
positive real-delivery and four negative-control cases to the owner's regression
suite. Keep the existing attribute, unlisted signature/body, public import,
target, forbidden axiom, sorry, ownership, cycle, compile, and probe checks. The
exception must come from the authoritative module/declaration registry.

## Files changed, backups, and commits

This pass changes only maintenance documentation and its diagnostic transcript:

- Local `REPORT.md` and `gate-reproduction.txt`, each with an initial `.bak`.
- Server `coord/reports/maintenance/A4-WeilConjectures.PoincareDuality.Poincare-1792292781.md`
  and `coord/reports/maintenance/A4-WeilConjectures.PoincareDuality.Poincare-1792292781-gate-reproduction.txt`,
  each with a `.bak` preserving its prior contents (empty for these new files).

Server commit: pending documentation commit under `SHEAF_LEAD=L-only` and
`coord/.merge.lock`, with author Bin Wu. Its SHA is recorded in the final local
report after committing; on the server it can be found with `git log -1 --` and
the maintenance report path above.

No protected script, registry, Lean module, dispatcher state, claim, review
service, or landing record was edited. Unrelated concurrent server changes were
excluded from this commit. No provider error is implicated in the reproduced
refusal. No process was killed, no `lake build` was run, and no cap, throttle,
admission limit, or pause was introduced.

## Next worker

Retain `/home/ubuntu/weil-sandbox/A4/WeilConjectures.PoincareDuality.Poincare`
and its `coord/changes/A4-poincare-tate-invertibility.md`. The current retained
set has eight modules and zero text-level sorries, including
`Sheaf.PoincareDuality.CompatiblePrimitiveRoots`; the previous maintenance
report's statement that this theorem remained open is now stale.

The landing-tool owner must install the gate fix above. Once the normal shared
repository refresh includes it, rerun
`python3 /home/ubuntu/weil-launcher/deliver3.py A4 WeilConjectures.PoincareDuality.Poincare --no-push`.
After that prints OK, use the normal delivery command without `--no-push`.
Do not discard or redo the retained mathematics, remove the invertibility repair,
or add duplicate exception entries. Any additional Lean validation must compile
one file at a time with `tools/lean_file.sh`, within 60 seconds.
