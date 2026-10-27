# Q52 native exceptional forgetful: repeated-failure diagnosis

2026-10-24, maintenance run 1792821458; returned head 3a0b8d629434.

The remaining failure is the protected delivery compiler's source selection,
not item mathematics or a provider error. The in-place source repair already
exists in commits 37e0d31483b and 1b93b6f81d6, with node formatting preserved
by d3d37b514e0. No additional mathematical change is indicated.

At 06:14 UTC the last published green build was still 54696378c797,
published at 03:53:24 UTC, before the repair. All four repaired modules have
existing published artifacts. For each, tools/nt_source_overlay.py returns
None from source_for_import: their newer committed mathematical interfaces
are intentionally excluded from its missing-artifact/header-conversion rules.
tools/nt_srv_compile.py therefore imports the old one-universe System.

A direct tools/lean_file.sh probe confirms the difference: the published
interface rejects System.{u,0}; the repaired private interface accepts it.
All four source hashes match those recorded in the previous successful
maintenance mirror. Fresh sequential tools/lean_file.sh checks in a new
private maintenance mirror passed with the standard 60-second limit:

| File | Seconds |
| --- | ---: |
| ConstructibleExceptionalAdjunctionCoefficientsData.lean | 51.7 |
| ConstructibleExceptionalCoefficientConstruction.lean | 34.7 |
| ConstructibleExceptionalCoefficientCoherence.lean | 30.2 |
| ConstructibleExceptionalAdjunctionCoefficients.lean | 18.4 |
| NativeExceptionalForgetful.lean, unchanged worker packet copied to scratch | 20.4 |

Temporary probes were removed. Only the private group mirror was populated;
no published artifact was changed. No full build was run.

The server buildloop log explains the publication lag. Builds after the
repair failed, most recently at 05:00:50 UTC on
Sheaf.Paper.AdicSmoothDualizingComplexes with a deterministic heartbeat
timeout and subsequent unknown identifiers. That module is quarantined for
rework. At inspection the independently running scheduled upstream sync
was building its own snapshot; this maintenance did not stop or alter it.
Those historical failures do not prove the Q52 repair caused them.

Required protected-tool change, if publication does not resolve the mismatch:
provide an explicitly authorized, exact committed dependency source closure
to both ordinary compilation and landing validation, consistently in
tools/nt_source_overlay.py source_for_import and overlay_sources and their
compiler callers. Preserve public node bindings and cache by source/import
content. Recompile affected importers consistently; do not mix old and new
artifacts. Acceptance requires the ordinary Q52 deliver2.py --no-push to
accept System.{u,0} and pass its standard checks. A normal green publication
containing the repair also resolves this specific mismatch.

The task explicitly forbids edits to landing tools; this note records the
needed change instead. No protected tool, dispatcher state, admission setting,
or process belonging to another session was changed. No delivery was pushed.

Next worker: preserve the current packet, public
ConstructibleExceptionalCoefficients.System.{u,0}, direct characteristic proof,
and original exceptional-inverse-image node binding. Do not restore the
duplicate NativeExceptionalCoefficientSystem or unowned Data overlay. The
item has passed compilation against current dependency sources. Its ordinary
delivery remains unvalidated until the compiler sees the generalized interface.
Recheck the published commit/source selection before attributing another
identical universe error to the item or reporting READY.
