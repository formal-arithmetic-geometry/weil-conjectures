## What changed

Replaced the remaining proof of `CategoryTheory.scalarHomTensorCoherence` in
`Sheaf.Algebra.Homology.ScalarHomTensorCoherence`; its public statement and
all public definitions remain unchanged. All new helpers are private and proved.

The proof checks the chain composition and identity equations on total pure
section generators. It extends the scalar-adjunction unit normalization from
flat K-flat resolutions to all complexes, identifies the canonical derived
adjoint comparisons with their chain counterparts, and pastes the normalized
tensor squares on K-flat pairs. Every derived object has a K-flat representative
up to isomorphism, so naturality transports both equations to all derived objects.

The node copy records this argument and its four retained proof dependencies.
The `TensorColimitsIndependentCoefficients` declaration supplies the comparison
between the two flatness conventions used for a resolving complex. The private
comparison APIs keep termwise maps and tensor routes abstract during elaboration.
The isomorphism-transport calculation is proved in abstract categories and then
applied to K-flat representatives. Unit normalization likewise uses general
categorical diagram lemmas; composition-exactness instances are scoped to their helper;
no definition or statement repair, public import change, consumer adaptation,
new module, or new node is included. The administrative change record
`coord/changes/H4-scalar-hom-tensor-private-proof-environment.md` records the
local elaboration commands and all consumers, as requested by delivery preflight.

## Proved and sorry left

Closed **1 of 1** original holes:
`CategoryTheory.scalarHomTensorCoherence`, node
`lem-sfb-scalar-hom-tensor-coherence`.

Remaining holes: **0**. Added holes: **0**. Split-off obligations: **0**.
The complete proof passed `lcompile.py` without warnings in **57.4 seconds**.
The final performance refactor proves the two unit-normalization diagrams in
abstract categories; both helpers and their concrete scalar-model applications
passed a focused check in **25.9 seconds**. The required delivery command checks
the final canonical module again before pushing. No axiom, hollow definition,
or holed private helper was introduced. Scratch diagnostics are outside `lean/`
and are excluded from the packet.

## No longer needed

Removed the proof import `Sheaf.Paper.ResolvingRepresentativeWhiskering` and its
node `lem-weil-pbc-resolving-representative-whiskering`: essential surjectivity
and naturality suffice for equality, so fullness of representative restriction
is unnecessary. Removed the unused original private uniqueness helpers
`complexIso_unique`, `tensorIso_unique`, and `comparison_unique`.

The revised node also omits three unused dependencies of the original plan:

- `lem-sfb-scalar-tensor-cancellation-independent`
  (`Sheaf.Algebra.Homology.ScalarHomTensorCancellation`): naturality along a flat
  K-flat resolution extends the unit equation without a preservation-of-flat-terms
  detour.
- `lem-pur-cochain-pullback-tensor-coherence`
  (`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`): the specified generator
  equations give the chain squares directly.
- `lem-weil-pbc-tensor-comparison-descent-representatives`
  (`Sheaf.Paper.TensorPullbackRepresentativeDescent`): the tensor comparisons are
  already natural isomorphisms, and equality descends by naturality along
  isomorphisms from K-flat representatives.

No module is withdrawn. These are dependencies this proof does not need;
other consumers can still require their modules.

## Where the brief, the DAG or earlier work was wrong

The earlier draft had an incorrect identity object in the final inverse
cancellation, treated a mapped-complex identity comparison as a strict identity,
and lacked the canonical restriction transports in its adjunction-composition
calculation. The corrected proof keeps these transports explicit and uses
proved component APIs. The complete public statement is preserved.

The original plan uses full faithfulness for an equality that follows already
from isomorphisms to representatives. It also makes the flat-term preservation
detour unnecessary once the unit equation is extended by naturality. The existing
theorem docstring retains the original plan; the editable node proof records
what the delivered argument actually uses.

The old unavailable-`Sheaf`-root compiler failure is resolved. Current requests
sometimes receive the compiler's busy-server response and are retried. No
launcher tool was modified or bypassed, and no local Lean or Lake was run.
The initial inspection accidentally ran read-only `git status --short` in the
shared repository; it changed no files, and no subsequent repository git command
was run. All edits are confined to the assigned sandbox.

Delivery preflight requested a change record for new local attributes and variable
commands, despite the unchanged public interface. The record is included; there
is no forced adaptation. The final canonical file passed the delivery compilation
and axiom audit before that administrative preflight refusal.

The next resumed session rechecked the retained proof against the current source:
the public theorem signature is verbatim unchanged, the node changes only its
proof fields, and the module has zero `sorry` tokens and no overlong lines.
Its required initial delivery invocation terminated with exit code 137 without
diagnostics. The unbuffered retry passed compilation and the axiom checks, then
crashed in `sharedrepo.worktree`: `git checkout -q --detach origin/sheaf-dag`
raised `subprocess.TimeoutExpired` after 600 seconds. No commit or push was reached.
The diagnostic is retained in `current-resume-delivery-failure.log`, outside the
packet. This is a delivery-worktree tool failure, not a Lean compilation timeout
or the compiler's busy-server response. No launcher script was modified.

The following resumed session again confirmed the unchanged public theorem
signature, zero remaining or added holes, no overlong lines, and changes only to
`proof`, `proof_deps`, and `proof_origin` in the node. Its required first delivery
invocation waited inside the tool and ended with exit code 137 without output.
The unbuffered retry received `no answer from the compile server within 210 s`;
this is the brief's busy-server condition, so compilation is retried after waiting.
No lock, launcher script, or shared-repository file was modified.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
