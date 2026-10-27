# F4 WeilTrace import maintenance — 2026-10-22

## Current scope — supersedes the Basic-only restriction

The 2026-10-23 B3 maintenance correction in `coord/changes/B3-WeilTrace-unit-maintenance.md` supplies the canonical unit API missing from the original repair. The item must replace `Main` by `Basic` AND add `public import Sheaf.TraceFormula.WeilUnit`. Every declaration, signature, docstring and proof body remains verbatim, including both inherited sorries. The `WeilBoundedConstructible.unit` construction was moved unchanged to this shared module; `Slop.Main` publicly imports it rather than declaring it twice. Do not deliver a second copy of the unit or import `Slop.Main` into WeilTrace. The earlier sections below are historical and their Basic-only instruction is superseded.

## Cause

The rework archive imports `WeilConjectures.TraceFormula.Main`, whose source is absent
from both `lean/` and `quarantine/`. This is an integration mismatch, before Lean
elaboration. Commit `4d41f09f2ed` moved the old model-Frobenius trace-formula modules
to `TraceFormula/Slop` and installed the PR #1473 base-point API at the canonical
`TraceFormula/Basic` path. The later sync `29fa402a64e` introduced `WeilTrace` with
the old `Main` import. A seven-module restoration (`02a9c520747`, landing
`20261021T100013-L-2606343`) was reverted in `614abd287f4` after a red build; its
missing paths must not be treated as available dependencies.

Workers correctly preserved the upstream archive, but the verbatim restoration
rule and the ban on creating upstream modules made this assignment impossible.
Repeated dispatches could only reproduce the missing-source rejection.

## Authorized repair

For this maintenance item, replace exactly:

```diff
-public import WeilConjectures.TraceFormula.Main
+public import WeilConjectures.TraceFormula.Basic
```

`Basic` supplies the base-point API used here (`point`, `toPoint`, `toPoint_ext`).
Keep every declaration, signature, attribute, docstring and proof body unchanged,
including the two existing sorries. No mathematics is assigned by this repair.
Do not substitute `TraceFormula.Slop.Main` or recreate the removed seven modules.
The other imports remain present. No declaration changes means no downstream
consumer adaptation is required by this import repair.

The two rows in `coord/upstream-statement-exceptions.tsv` authorize removal of the
old public import AND addition of the new public import. Both are necessary:
`stage3_gate.py` checks the symmetric difference of the public imports.
`stage3_delivery.py` also consults this table for the rework verbatim exception.
No tool or gate is changed or bypassed. The quarantine archive stays intact.
The item's `coord/rework.tsv` cause now includes this explicit repair instruction.

## Next worker

Retain the import-only corrected source prepared in the F4 sandbox, or copy the
archive and apply the exact substitution above. Read the exception table and this
record before concluding that verbatim restoration forbids the correction. Deliver
through the normal stage-3 path. The rework row and quarantine archive stay until
a green build verifies restoration; do not retire the item or remove either row.
Existing missing published dependency artifacts or dependency compilation errors
are separate from the source-import repair; record the actual module and diagnostic.


## Compiler-service scanner repair

After the authorized import migration a worker reached another deterministic
pipeline failure: the private overlay tried `ShriekComposition` without first
supplying `Derived.UpperShriek`. The embedded line scanner in
`tools/remote_compile_set.py` stopped at `public import` with the module name on
the next line. On the actual ShriekComposition source it saw only the first
Mathlib import and lost the following seven imports, including UpperShriek.

`header_imports` now uses the existing comment-aware `import_cycles.imports`
parser for both dependency planning and cache keys. The actual source now yields
all eight imports. No source gate, source-integrity check, admission setting,
concurrency limit or file timeout is modified. The local `lset.py` entry point
reads this versioned service from the shared clone; the server's `cc1/rset.py`
executes this service directly, so both paths receive the same repair.

`tools/tests/test_remote_compile_dependencies.py` has a service-level regression
with a wrapped import followed by another public import, nested comments and a
string containing a fake import. It verifies the dependency compile order,
caller artifact selection and subsequent cache reuse. It failed before the
repair (B and C were missing) and all seven dependency-service tests pass after.
The regression uses mocked compiler processes and starts no Lean build.

Single-file Lean validation of the import-only candidate was attempted separately
using `tools/lean_file.sh`, serially with the unchanged 60-second limit. Following
the absent artifacts reached the existing
`WeilConjectures.PoincareDuality.ProjectionFormula` source, which timed out at 60
seconds. Thus neither a complete WeilTrace Lean compile nor a successful landing
is claimed. This timeout is distinct from both repaired pipeline failures; the
next worker should record current compiler diagnostics rather than reuse an old
missing-Main or truncated-import-scanner blocker.


## Follow-up maintenance: shared root rollback, 2026-10-22 04:05 UTC

The historical missing-UpperShriek diagnostic predates scanner repair
`18a85f68430ebdf323dcf4b7824b2836049ad762`. The current compiler planner includes
UpperShriek before ShriekComposition. All seven dependency-service regression
checks pass. An inspection before the subsequent rollback planned 58 unpublished
prerequisites, beginning with PoincareDuality.ProjectionFormula. Both its direct
60-second tools/lean_file.sh check and the current worker's private-overlay check
timed out. This does not certify any later module or justify restoring unverified
objects into publication. No Lean source or proof was changed by this follow-up.

A separate landing defect changes which prerequisites exist at all.
`tools/rework.py::cluster_restore` creates one landing per restored source module,
but puts the shared WeilConjectures.lean root import edit in every such record.
`tools/landing.py::drop_plan` then chains every later record sharing that file
when any earlier record is dropped. Consequently nominally independent module
restorations are one rollback chain. This contradicts cluster_restore's stated
intent to remove only failing modules and their actual importers.

Concrete evidence: closed record `20261022T032502-S-2310895-151` contains both
WeilConjectures.lean and PoincareDuality/ProjectionFormula.lean. At 03:58:07 UTC it
was reverted because it shared a file with record `...-150`; the recorded build
failures were ClosedAdjointConstructibleYoneda and
CompactificationRefinementLocalizing, not ProjectionFormula. Commit
`80c0d4bd74e` dropped 108 landings and `74661519a7f` dropped another 39. The next
F4 attempt then failed the source gate on TraceFormula.Basic and
WeilObject.BoundedConstructible.LowerUpperShriek. At 04:00:05 UTC the dispatcher
released WeilTrace because the current target route no longer reached it. This
release is not a successful restoration or proof, and it does not authorize
withdrawing its archive. A later automatic restore has already brought
ProjectionFormula back; existence in the live tree is not green publication.

A read-only reproduction of the actual drop_plan function used three independent
module records sharing the root import file. Requesting removal of only the
first returned all three. The reproduction changed no repository state.

### Required correction in protected landing tools

Make additions to an import-only root compose and roll back independently of
unrelated source-module restorations. The surviving root imports must be derived
from the surviving source set, without chaining unrelated modules merely because
they added different root import lines. Keep ordinary same-file rollback
protection for real source edits and remove actual importers of removed modules.
Test an early restored-module failure with two independent later restores and a
true importer: independent modules and their root lines must survive, while the
failed module and its importer are removed. Validate the resulting snapshot's
imports as well as its live sources. This is a correctness change, not an
admission rule or a reason to delay dispatch.

The maintenance instruction explicitly forbids editing landing tools, so
cluster_restore, drop_plan, the batch lander and the launcher were only read.
This required code correction is reported for the owner of those tools.

### Next worker after this follow-up

Keep the exact authorized Main-to-Basic substitution and both original sorries.
Read current rework, claim, source and publication records before interpreting a
historical failure: the scanner fault, a real dependency elaboration timeout and
a source removed by rollback are distinct. Do not copy arbitrary cached objects
into publication, resurrect Slop/Main, delete quarantine or claim a completed
WeilTrace compile. Use the normal delivery checks against the current source set.
No dispatcher state, claim, rework hold, retry count or concurrency setting was
changed by this maintenance.
