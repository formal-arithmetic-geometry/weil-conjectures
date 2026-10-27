# Q52 native exceptional forgetful maintenance

The returned item `lem-sf-weil-native-exceptional-forgetful@3a0b8d629`
repeatedly stops before compilation: `deliver2.py --no-push` rejects its
in-place `ConstructibleExceptionalAdjunctionCoefficientsData.lean` repair
because no sandbox node has that module as `lean.file`. The public System
definition node names the public facade and is an `existing` declaration.
Rebinding it to a copied native-only record caused RETURN 2 and is not a fix.

Install the shared dependency repair separately from the item delivery.
The four existing coefficient modules retain their names, definitions,
actual categories, System fields, and constructive exists_system assembly.
The closure has its own universe v; the scheme/stage family uses max u v.
The original same-universe case specializes at .{u, u}; the native closure
PadicAlgCl l specializes at .{u, 0}. Explicit universe arguments prevent
elaboration from searching through underdetermined max constraints.
No new axioms or sorry declarations are introduced; the pre-existing
construction and coherence theorem placeholders are unchanged.

The five existing node records have only their stored Lean signatures
updated to match; bindings, public names, dependencies, and prose remain.
All changed production files have adjacent .maint-Q52-1792812318.bak copies.

Validation before installation: the four dependency modules followed by the
worker's NativeExceptionalForgetful module passed server file compilation
one at a time with the standard 60-second Lean limits. The consumer uses
the original System.{u, 0}; no duplicate NativeExceptionalCoefficientSystem
is needed. Its main theorem retains its single stage-2 sorry.

Next worker: remove the now-obsolete Data overlay from the item packet,
refresh def-weil-exceptional-inverse-image from the server, use the original
public System.{u, 0}, and run the normal deliver2.py --no-push check.
RETURN 1's inline coefficientCharacteristic instance is already present
in the repaired sandbox; do not restore the lisse-extension statement
dependency. The earlier report's ownership blockers describe the old base.

No dispatcher, provider, review, admission, or landing tool was changed.
The maintenance workspace holds detailed validation logs and REPORT.md.

## Final verification and protected-tool handoff

Follow-up commits: d3d37b514e0 restores the existing JSON formatting without
changing content; 1b93b6f81d6 supplies explicit universe arguments on ring
inclusions. The latter removes residual elaboration searches. Direct installed
tools/lean_file.sh checks (one at a time, 60 s) pass: Data 33.8 s, Construction
15.1 s, Coherence 7.9 s, public facade 6.3 s, unchanged existing
IntegralExceptionalInverseImage consumer 16.2 s. The native consumer also
passes with all four source overlays in the normal stage-2 compiler.

The ordinary deliver2.py --no-push now clears module ownership but still
fails with too many explicit universe levels for System at lines 250/368.
The last published green build, 54696378c797 (2026-10-24 03:53:24 UTC),
contains the old one-universe System. tools/nt_source_overlay.py selects
current source only for missing artifacts, unbuilt source-library modules
and identical-body module-header conversions; it ignores committed interface
changes with existing artifacts. The normal compiler therefore cannot see
this repair, although direct and explicit source-overlay checks pass.

This maintenance is explicitly forbidden to edit landing tools, shared build
artifacts or run lake build. The protected tool owner needs a source-hash-keyed
path for the exact maintenance-authorized committed source/dependent closure
without rebinding existing public nodes. A normal green publication containing
this repair also resolves the stale artifact. REPORT.md in the launcher
maintenance workspace has the reproduction and full path/commit inventory.
Keep the sandbox's System.{u,0} and do not restore the Data overlay or copied
native System. Earlier blockers describe the old packet. No delivery was pushed.
