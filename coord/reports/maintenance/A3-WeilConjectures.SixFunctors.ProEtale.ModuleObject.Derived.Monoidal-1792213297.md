# WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal maintenance

Status: cause confirmed; the required corrections are in protected stage-3 gate/report tooling.
Those tools and the Lean module were left unchanged because this maintenance task forbids editing
review and landing tools. No mathematical repair was delivered or claimed.

## Cause

The assigned module's remaining holes are carried by five existing declarations whose Lean
keywords are `def` or `instance`: `upperStarTensorCounit`,
`leftDerivedUpperStarTensorLeftCounit`, `isLeftDerivedFunctor₂_upperStarTensor`,
`isIso_leftDerivedUpperStarTensor`, and `monoidal_leftDerivedUpperStar`. The retained sandbox
proof closed all nine fields and compiled, but `tools/stage3_gate.py` rejects every changed
non-theorem body solely because its old keyword is not `theorem` or `lemma`. The dispatcher counts
repeated tool refusals rather than mathematical failures. The earlier D4 landing only closed
`upperStarTensorComplexHom_comm`.

A read-only synthetic check against the live gate gives `REFUSE` for a sorried `def` changing from
`sorry` to a proof, while the analogous `theorem` is accepted, even with unchanged signature and
attributes and a decreased sorry count. The retained delivery diagnostics show the same refusal.
The candidate also adds public helper declarations and a public import; those are separate valid
interface refusals and must remain guarded.

A second contract mismatch is present in the same dry run: preflight requires an author report to
contain `## Second reading by A3`, while the worker brief reserves that section for the independent
reader and tells the author not to write it. The retained dry-run findings record both failures.

## Required owner change

The owner of `tools/stage3_gate.py` must reconcile the source-library freeze with queued proof
holes in proposition-valued `def`/`instance` carriers. A narrow authorization should allow an
unchanged-signature, unchanged-header body replacement only when the baseline declaration already
contains the assigned `sorry` (ideally after confirming that its declaration type is a proposition),
while continuing to reject data-valued construction edits, statements, attributes, public
additions, public imports, and new or hidden sorry. Compile, import-cycle, and axiom checks must
remain mandatory. Separately, `deliver3.py`/preflight needs an explicit author-dry-run mode that
defers the independent-reader section check; final reader delivery must still require that section.
This maintenance task forbids applying either landing-tool change here.

## What changed

No protected tool, dispatcher file, Lean module, DAG record, node, brief, permission, admission
setting, throttle, pause, or worker process was changed. A temporary candidate gate patch was
prepared only for diagnosis and reverted immediately; its audit commits are recorded in the local
maintenance report. This incident record and its backup are the only project artifacts from this
maintenance run.

## Validation

The retained sandbox compile transcript reports exit code 0 in 48.5 seconds
(`scratchpad/tenth-retry-compile.log`). The unchanged server source compiled with the mandated
single-file tool in 39.4 seconds. A fresh dry-run invocation reached its local compile step but hit
the existing 60-second timeout before preflight; it pushed nothing. No `lake build` was run and no
process was killed.

## Next worker

After the owner lands both narrow tooling fixes, move the retained public helpers into allowed
`Sheaf` helper modules or replace them with existing declarations, use private imports where only
proof bodies need them, restore unchanged bodies for already-proved definitions, and rerun the
mandated one-file 60-second compile and dry run.
