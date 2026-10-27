# Q24 maintenance: exceptional refinement mates

Status: source/publication mismatch confirmed; ordinary delivery is still blocked.
No item mathematics, library source, DAG record or compiled shared artifact was changed.

## Cause

The existing in-place repair of the exceptional coefficient interface is on server
main, but is absent from the last green publication. The worker source reader
(`batch2/scompile.py --source`) returns current source; the ordinary compiler uses
published artifacts for these modules. Current source therefore advertises
`Operation.{u, v}`, `C.{u, v}` and `RingStage.inclusion.{u, v}`, while the imported
published interface has one universe. The worker's two-universe packet cannot
pass its ordinary dry run in that environment. Repeated identical retries do not
indicate a failure of the lemma's mathematics or justify suppressing dispatch.

Inspection at 2026-10-24T21:40:14Z found publication
`54696378c79742b8b42dd2c10a62ac848ec9535c` (green, 2026-10-24T03:53:24Z).
All four current sources match HEAD, differ from their published blobs, have
existing artifacts, and are excluded by `source_for_import` (returns None):

- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData`
- `Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction`
- `Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`

The repair commits are `37e0d31483b` (independent coefficient-closure universes)
and `1b93b6f81d6` (explicit inclusion universes), with node formatting preserved
by `d3d37b514e0`. The buildloop registered them as interface landings
`20261024T041149-U-1499443-315` and `20261024T044910-U-2691633-536`.
Thus re-registering the same source edit is not the repair. Recent global builds
remain red and publish nothing. This note does not attribute their unrelated
failures to this interface change.

## Fresh validation

Sequential `tools/lean_file.sh` invocations in the new isolated group
`maint-Q24-refinement-1792877468`, with the normal 60-second per-file limit:

1. An import-only module checking the existing public
   `ConstructibleExceptionalCoefficients.Operation.{0, 1}` failed with
   "too many explicit universe levels" in 4.5 seconds.
2. The unchanged current Data source compiled into that group's private mirror
   in 38.4 seconds with no warnings.
3. The identical import/check module then passed in 3.7 seconds.

This proves the interface mismatch without rewriting mathematics or shared
artifacts. The temporary probe and its .bak are under
`lean/.sandbox/maint-Q24-refinement-1792877468/`.
It does not make the ordinary delivery use that maintenance mirror.

The preceding worker's immutable log also records the actual two-file
`scompile.py` experiment: exact current Data source plus retained item passed
sandbox and library checks (item 33.1 s and 15.7 s). That is historical evidence,
not a new ordinary dry-run success or mathematical approval.

## Required protected repair

The maintenance instruction explicitly prohibits changing landing tools and
requires describing the needed change instead. Operative selection is in
`tools/nt_source_overlay.py:source_for_import` and `overlay_sources`, used by
`tools/nt_srv_compile.py` and `tools/nt_compile.py`, together with landing
validation. The owner must provide a coherent, explicitly authorized committed
source closure for this existing interface repair, shared by worker compile,
preflight, review and landing. Include affected importers, such as
ExceptionalFiniteOperations and ExceptionalFieldDescent, so old consumer
artifacts cannot be combined with the new interface. Key snapshots and caches
by exact sources and dependency inputs. Preserve original public declarations
and node ownership; no duplicate Data module, fabricated owner or weaker
universe restriction is a repair.

The other supported resolution is a verified green publication containing the
already committed repair through the existing global-build machinery. This
maintenance may neither edit the protected landing path nor run `lake build`.
It does not mutate publication metadata or promote private .olean files.

Acceptance: a clean ordinary compiler request accepts `Operation.{0, 1}` and the
retained packet passes `deliver2.py Q24 lem-sf-exceptional-refinement-mates
--no-push` without supplying a diagnostic dependency copy. Complete the
outstanding mathematical self-review before any actual delivery.

## Next worker

Retain the packet and its independent universes, `ringInclusionShift`, explicit
universe arguments, scoped transparency options and repaired line layout.
The saved report still requires review of Transport's normalization assumptions;
a passing diagnostic compile does not settle that review. Follow the ordinary
dry-run/delivery brief. Do not deliver the scratchpad dependency, add its
upstream owner as a prerequisite (that would create a DAG cycle), or identify
independent universes to accommodate an old artifact.

The launcher route note now supplies this diagnosis to future attempts. No
claim, dispatcher count/state, retry policy, concurrency setting, admission
limit, throttle or pause was changed. No running worker was stopped. No
provider problem was identified as the cause, and no provider setting changed.
