# Maintenance report: WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

## Cause

The repeated failure is a shared stage-3 gate defect, not a Lean proof, record, permission,
or provider failure. The gate in `tools/stage3_gate.py` line 92 (introduced by commit
`b58a93234bd`) computes

```python
data = [k for k in d["body_changed"] if d["old"][k]["kw"] not in ("theorem", "lemma")]
```

and rejects every changed body in an adopted `WeilConjectures` module unless the old
keyword is `theorem` or `lemma`. The item has seven unchanged-signature declarations whose
keywords are `instance`, but whose types are propositions and whose bodies are proofs:

- `AddCommGrpCat.hasFunctorialFlatResolution`
- `AlgebraicGeometry.ProEtale.weaklyEtale_toSpecZ_profiniteToScheme`
- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_profiniteToProEt`
- `AlgebraicGeometry.ProEtale.hasLeftKanExtension_op_profiniteToProEt`
- `AlgebraicGeometry.ProEtale.isIso_η_pointUpperStar`
- `AlgebraicGeometry.ProEtale.isIso_δ_pointUpperStar`
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarFromPointComp`

The retained sandbox replaces only those seven proof bodies, adds three private proof
imports and four private helpers, and leaves all existing signatures, definitions, public
imports and instance heads unchanged. The required dry run reaches the upstream preflight
and is rejected before compile/probe with exactly: `stage3_gate.py:92 ... changes the body
of non-theorem declaration(s) ...`. The five failed attempts in the initial dispatcher
state all report this same refusal; a sixth attempt was launched while this maintenance
run was investigating and inherited the same handoff.

## Changes and commits

No launcher-owned review or landing tool was edited. The complete proof already present in
the sandbox was retained at
`/home/ubuntu/weil-sandbox/C2/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
No source Lean file, DAG record, dispatcher state, retry policy, or claim was changed by
maintenance. The permitted fix is a maintainer change to the gate: it must allow a body
replacement when the old and new declaration signatures are identical and the declaration
type elaborates to `Prop`, including proposition-valued `instance`s, while continuing to
reject data-carrying instance/definition changes. This report is the requested record of
that change; the gate itself remains untouched because the instructions reserve review and
landing tools to the maintainer.

A maintenance report was committed on the server under the merge lock:
`coord/reports/maintenance/C2-WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic.md`.
The commit is recorded in the final response and contains no source or tool change.

## Validation

- `python3 /home/ubuntu/weil-launcher/lcompile.py` compiled the retained Basic module in
  3.9 seconds with exit code 0.
- The retained module contains no `sorry` tokens in declarations. Its earlier axiom probe
  reported only `propext`, `Classical.choice` and `Quot.sound`.
- The shared source and server source have the same current hash and still contain the
  seven original `sorry` bodies; the sandbox diff is limited to the proof work described
  above.
- The required `tools/lean_file.sh` invocation did not reach Lean on this machine: its
  initial `lake env printenv` attempted to bootstrap missing package clones. That command
  was terminated only as a process started by this maintenance run; no unrelated process
  was signalled. The independent `lcompile.py` check completed successfully.
- No `lake build` was run, and no provider HTTP/concurrency error occurred.

## Next worker

Keep the sandbox proof and this diagnosis. After the maintainer updates the stage-3 gate to
recognize unchanged proposition-valued instance proofs, rerun the required
`deliver3.py C2 WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic --no-push` and
then deliver the retained proof. Do not rename the instances, alter their statements,
change public imports, or work around the gate by adding duplicate theorems; those would
change the adopted source interface and are the wrong fix.
