## What changed

Restored the assigned quarantined module
`Sheaf.Paper.CoefficientTowerShriekInterfaces` at its original Lean path, preserving
all its public declarations, structure fields, defining terms and public imports.
The original global disable/re-register pair for the generic essentially-small
sheafification instance is replaced by a section-scoped removal. The inherited
instance is restored automatically when the section ends. The coefficient-universe
elaboration environment inside the interface remains the same.

Change record:
`coord/changes/B2-coefficient-tower-shriek-interface-restoration.md`.
The existing node `def-sp-coefficient-tower-shriek-interfaces`, its Lean attachment,
statement dependencies, and the unit route remain unchanged.

## Proved and sorry left

This is an assigned definition repair with zero holes. Original `sorry` count: 0;
closed: 0; added: 0; left: 0. No theorem is split off. All original explicit
constructions remain explicit constructions.

The unchanged archived module compiled on the project server in 15.8 seconds.
The scope behavior was independently checked in a small Lean file: after removing
`instAddNat` inside a section, `#synth Add Nat` succeeds after the section closes.
The repaired interface and all four unchanged archived consumers compiled together
in import order on the server. The reported wall times were 86.3, 54.5, 54.0, 55.6
and 71.3 seconds respectively; all five returned success, with no Lean diagnostics.
Only the interface is delivered; the consumer copies were moved out of `lean/`
after these compatibility checks. The delivery tool performs the final axiom probe
and preflight.

## No longer needed

None. No import, declaration, node, module, or planned dependency is pruned. In
particular, the four quarantined consumers remain needed. They were checked from
their archived source rather than treating their absence from `lean/` as withdrawal.

## Where the brief, the DAG or earlier work was wrong

The item contains no `sorry`; the rework assignment is restoration of its definitions.
The old cluster-build diagnostic does not reproduce against the current published
server build: the unmodified archive compiles. The packet nevertheless makes a
concrete elaboration-scope repair rather than only rebasing or returning an empty
module. It removes the explicit global instance re-registration and scopes the
existing instance removal, preserving the intended importer environment.

The first local-service compile failed because its mirror lacked `Mathlib.olean`;
explicit server compilation succeeded. An attempted `[local -instance]` spelling
was rejected by Lean and replaced by the tested enclosing-section form. Neither
failed experiment is included in the delivered module. Provider interruptions did
not change the sandbox or result in a push.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
