# Maintenance report: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal`

Date: 2026-10-17. Group `C2`, stage 3. Dispatcher key:
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal@new`.

## Outcome

The repeated post-provider failures are a protected stage-3 submission-tool defect.
The worker sandbox contains a zero-sorry repair, but the normal `deliver3.py --no-push`
preflight rejects it before push. I did not edit the shared gate, delivery, review, or
landing tools because the project contract (AGENTS.md sections 3 and 6) requires a
worker to report a tool that refuses correct work. The item is therefore not landed;
the completed repair is retained for the next worker after the gate owner makes the
semantic correction.

The first recorded attempt (`1792236590`) was an HTTP 429 provider failure. That is an
external provider failure and was not changed. The remaining counted attempts repeat the
same deterministic gate refusal, so the pipeline defect is the stage-3 gate described
below, not provider capacity, permissions, or Lean mathematics.

## Cause

The server file `tools/stage3_gate.py` currently decides whether an upstream non-theorem
body is safe to change with:

```python
data = [k for k in d["body_changed"]
        if d["old"][k]["kw"] not in ("theorem", "lemma")
        and not s3.only_sorry(d["old"][k]["body"])]
```

`only_sorry` examines the *entire old declaration body*. The dispatched module has seven
existing holes nested in three partially constructed declarations whose data fields are
already present:

- `AlgebraicGeometry.ProEtale.CondensedRing.upperStarTensorCounit`: two naturality fields;
- `AlgebraicGeometry.ProEtale.CondensedRing.leftDerivedUpperStarTensorLeftCounit`: two
  naturality fields;
- `AlgebraicGeometry.ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`:
  `associativity`, `left_unitality`, and `right_unitality`.

Each enclosing declaration is a `def` or `instance`, and its old body is not exactly
`sorry`, so filling only these proposition-valued proof fields is classified as changing
the non-sorry body of a non-theorem declaration. The source module's retained repair
also exposes helper declarations and imports needed by that repair; those diagnostics
are secondary. A proof-field-only rewrite cannot satisfy the current whole-body test.
There is no applicable entry for this module in
`coord/upstream-statement-exceptions.tsv`.

This is reproducible in the current server checkout (`HEAD` at inspection):
`deliver3.py C2 WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
--no-push` reaches preflight and returns `(c) stage3 gate`; the complete diagnostic is
retained in the worker sandbox at
`scratchpad/dryrun-20261017-2256.log`. Earlier attempts and
`/home/ubuntu/weil-launcher-all/dispatch.log` report the same refusal. The current gate
is also called by both the author preflight and the landing path, so changing only a
worker brief or rerunning delivery cannot resolve it.

## Repair retained and verification

The retained source is:

`/home/ubuntu/weil-sandbox/C2/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal/lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/Monoidal.lean`

Its worker report records all seven original `sorry` terms closed, with no new holes;
the revised module compiled as a single Lean file in 36.1 seconds, and the unit-coherence
consumer compiled. The final dry run reaches preflight only after the delivery script's
compile and axiom-probe phase. No delivery was pushed. Existing worker evidence and the
change record are retained in the sandbox:

- `report.md` and `coord/changes/C2-derived-module-tensor-counits.md`;
- `scratchpad/dryrun-20261017-2256.log` and earlier dry-run logs;
- the source module above.

No Lean source, DAG node, exception list, dispatcher file, review service, landing tool,
concurrency setting, queue, or retry policy was changed in this maintenance run. No lake
build was run and no process was killed.

## Required protected-tool change

The owner of the protected stage-3 gate must replace the keyword/whole-body test with a
semantic check that accepts an unchanged-signature replacement of existing **Prop-valued
proof fields** in a `def` or `instance`, while continuing to reject construction-data
changes. The check must elaborate the complete declaration type (including binders and
universes) in the baseline and delivered environments; a worker-supplied textual flag is
not sufficient. Keep the existing checks for signatures, attributes, visibility, public
imports, public declarations, cycles, sorry progress, compilation, and axioms.

Regression coverage should accept these seven proof completions, while still rejecting a
data-valued field, a missing elaboration result, changed signatures/attributes/public
imports, and a new `sorry` in an already proved declaration. The ordinary final delivery
must still require its independent reader where applicable. No special-case exception for
this module and no change to dispatch frequency, admission, capacity, throttling, or
retry policy is needed.

## Next worker

Keep the zero-sorry sandbox repair and its change record; do not redo the mathematics or
bypass the gate. Once the protected gate is corrected and visible in the delivery
worktree, rerun:

```sh
python3 /home/ubuntu/weil-launcher/deliver3.py C2 \
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal --no-push
```

Then inspect any remaining diagnostics. The prior worker's report says that the helper
and public-import changes may need to be moved to proof-private imports or otherwise
made compatible with the upstream policy after the semantic proof-field allowance is
installed. A successful preflight is required before any push or landing.

## Files and backups

- This report: `REPORT.md`; backup: `REPORT.md.bak`.
- Server maintenance record: `coord/reports/maintenance/C2-WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal.md`;
  backup: same path with `.bak`.
- No other tracked file was changed.
