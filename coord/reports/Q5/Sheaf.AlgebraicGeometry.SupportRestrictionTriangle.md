## What changed

Withdraw `lean/Sheaf/AlgebraicGeometry/SupportRestrictionTriangle.lean` under step 8d
of the dispatched brief. The current route uses `NormalizedSupportTriangle` and no
declaration calls the older `AlgebraicGeometry.Etale.supportRestrictionTriangle`.
Remove its public import from `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle`
and its proof import from `Sheaf.AlgebraicGeometry.SupportedProductLocalization`.
The change record is `coord/changes/Q5-withdraw-unused-support-restriction-triangle.md`.

Repair the return at `51f08d1875`: the change record now names the adapted module
`Sheaf.AlgebraicGeometry.SupportedProductLocalization` and its holder V2, replacing
D3. Refresh both consumers from current main before removing their import, preserving
subsequent import migrations. The former third importer `KunnethSupported` is already
absent on current main; remove its stale sandbox copy from this delivery.

## Proved and sorry left

Original item: 1 hole, in `AlgebraicGeometry.Etale.supportRestrictionTriangle`.
Proved: 0 of 1. Removed by withdrawal: 1. Retained item holes: 0. Added holes: 0.
This is pruning, not a proof or decomposition. Existing holes in the two consumer
modules are unchanged; no new statement or split module is delivered.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.SupportRestrictionTriangle`; pruned declaration:
`AlgebraicGeometry.Etale.supportRestrictionTriangle`. Remove both remaining imports:
public in `NormalizedSupportTriangle`, proof-only in `SupportedProductLocalization`.
The former third importer `Sheaf.AlgebraicGeometry.KunnethSupported` has already been
removed independently on current main and is not restored or counted as new pruning.
No other imports are changed relative to current main.

Do not prune `lem-pur-support-restriction-triangle` or its proof dependencies: its
current Lean attachment and normalized interface remain necessary. No unit statement
or step is bypassed. The unit's realized lists are unchanged.

## Where the brief, the DAG or earlier work was wrong

The item was still reached through imports although its theorem had no consumer.
The DAG node already attaches to the stronger `NormalizedSupportTriangle` interface.
The former note that the normalized module retains the existence theorem by import
is updated to record its withdrawal. The normalized mathematical statement, six-step
proof plan and dependency lists are unchanged.

The returned packet incorrectly recorded D3 as holder of `SupportedProductLocalization`;
the required V2 attribution is now explicit in the change record and below.

## Forced adaptations

`Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` (P1) and
`Sheaf.AlgebraicGeometry.SupportedProductLocalization` (V2): each loses only the
import of the withdrawn item. No signature, visibility, proof or other line changes
relative to current main. These removals implement the explicit step-8d withdrawal
and step-8b requirement to change every importer in the same delivery. There is no
original Lean compiler error: the delivery leaves an empty module, so the old imports
could still elaborate, but the withdrawal gate forbids any remaining importer.
The delivery tool recognizes import-only adaptations and records them for independent
review. Both adapted modules are verified together using the remote compiler.

## Forced adaptations

### Sheaf.AlgebraicGeometry.SupportedProductLocalization
Only imports removed (Sheaf.AlgebraicGeometry.SupportRestrictionTriangle), e.g. to break an import cycle; nothing else changed. CODEX verifies that the removal is needed.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
