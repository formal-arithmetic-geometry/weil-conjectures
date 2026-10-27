# B3 WeilTrace canonical unit API maintenance — 2026-10-23

## Cause

The F4 import repair in 30c8f8259e7 replaced missing TraceFormula.Main with Basic,
but Basic exports only the point API and WeilBoundedConstructibleOfEnd. The unchanged
WeilTrace.weilStalkSupertrace_unit statement needs WeilBoundedConstructible.unit,
whose only definition was in TraceFormula.Slop.Main. The Basic-only maintenance
restriction therefore made the repeated unknown-constant error unavoidable.
This is a source integration and maintenance-scope defect, not a mathematical task.

## Old and new

Move the existing canonical unit, including its original docstring, full name,
parameters, type and complete IsoAlgebra.mk body, unchanged into
lean/Sheaf/TraceFormula/WeilUnit.lean. It imports only
WeilConjectures.WeilObject.BoundedConstructible.Defs. Slop.Main publicly imports
this module and removes its local copy; every other declaration and proof is
unchanged. This is a maintenance relocation preserving the API, not removal of
the constant or a new mathematical definition. No holes are added or closed.

The authorized WeilTrace restoration now has exactly two import edits relative
to quarantine: replace public import WeilConjectures.TraceFormula.Main by
WeilConjectures.TraceFormula.Basic and add public import Sheaf.TraceFormula.WeilUnit.
All remaining text stays byte-identical. The rework row, both old import exception
reasons, and a third exception for the new public import record this scope.
This supersedes the previous Basic-only restriction; importing Slop.Main into
WeilTrace is still unnecessary. Do not recreate the obsolete seven Main modules.

## Users

- WeilConjectures.TraceFormula.Slop.Main: imports the extracted unit at the same
  full name and uses the same constructor, including its existing rfl proofs.
- WeilConjectures.TraceFormula.WeilTrace: add the authorized public import;
  its statement and both inherited theorem holes remain unchanged.
- WeilConjectures.TraceFormula.Statement (quarantined): receives the same public
  unit through WeilTrace when its separate restoration is retried; no source edit
  is needed for the unit relocation.

## Validation

The extracted constructor compiled alone before integration. Single-file checks
with tools/lean_file.sh (60 seconds per file) then compiled the new WeilUnit,
the adapted Slop.Main, and the exact quarantined WeilTrace with the two authorized
import edits, in that order. The Slop prerequisites were compiled serially against
the published build beforehand. No lake build was run. A declaration-level diff
verified that Slop.Main changes only its unit's location and the public import;
all its other statements and bodies are unchanged. The unit declaration text is
copied verbatim. The existing rework archive remains intact.

## Status

landed as maintenance integration; awaiting the normal global-build verification.
The item itself remains a B3 rework delivery; this maintenance does not retire its
row, archive or claim. The API relocation is one paired interface landing, so its
two source files are taken out together if verification fails.

## Next worker

Read this current scope even if an inherited prompt still quotes Basic-only.
Keep exactly the two authorized import edits and both original sorries:
finite_frobeniusFixedPoints and weilStalkSupertrace_unit. Use the normal delivery
path; no new node or mathematical proof is required for this import restoration.
Do not include the Slop.Main relocation again: it is already committed by
maintenance. Keep quarantined dependents as separate rework items.
