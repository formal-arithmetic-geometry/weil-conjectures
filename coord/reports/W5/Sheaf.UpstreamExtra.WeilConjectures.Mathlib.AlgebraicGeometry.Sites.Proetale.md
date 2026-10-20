## What changed

Restored `lean/Sheaf/UpstreamExtra/WeilConjectures/Mathlib/AlgebraicGeometry/Sites/Proetale.lean`
from its current `quarantine/Sheaf/` counterpart, as assigned by `coord/rework.tsv`.
For the return of delivery `f2bfe446d0` (base `e0d550965`), read the current server
source again: the live path is absent and the quarantined source matches this shared
checkout byte for byte (SHA-256
`fff5a13e7bb54695825110ba965723dcc1fd53948052f86b7c844efaa4761b1f`).
Copied that current source into the sandbox and reapplied the syntax repair; the delivery tool selects a fresh `origin/sheaf-dag` base.
Removed one orphan `variable (X) in` and three orphan
`set_option backward.isDefEq.respectTransparency.types false in` commands left when the
scheduled upstream sync extracted declarations. Wrapped the existing module comment to
100 columns. All three instance signatures, attributes, proofs, and all public imports
are preserved. No source-library file changed.

The freshly copied current source reproduced `Unexpected name OverMap after end` at
line 107 and subsequent scope errors with `lcompile.py` (1.4 seconds, exit 1).
After the repair, the same file compiles without warnings (1.7 seconds, exit 0).
Delivery preflight also checks declaration axioms.

Change record: `coord/changes/W5-Proetale-orphan-scopes.md`.

## Proved and sorry left

This is a syntax repair with zero holes before and after, not a new mathematical proof.
Holes closed: none (0 of 0). Holes added: none. Holes remaining: none.
The existing proved instances are:

- `AlgebraicGeometry.Scheme.ProEt.Proetale_hasIsos`;
- `AlgebraicGeometry.Scheme.ProEt.Proetale_isStableUnderComposition`;
- `AlgebraicGeometry.Scheme.ProEt.Proetale_isStableUnderBaseChange`.

## No longer needed

No imports, declarations, nodes, or modules pruned. Only orphan command prefixes were
removed. These scoped options no longer have declarations to govern; their original
subjects are now supplied by the publicly imported upstream module.

## Where the brief, the DAG or earlier work was wrong

The assigned module is quarantined, absent from `lean/`, and has no attached DAG node.
`coord/rework.tsv` identifies its original path and compiler error; the quarantine copy
is the baseline for this repair. There is no theorem with `sorry` to prove in this item.
The sync retained scoped command prefixes after extracting their declarations, making
otherwise complete instances unavailable through this module.

The returned delivery `f2bfe446d0` was refused because the live file changed after
its base `e0d550965`.
This retry reconstructs the repair from the current quarantined source and checks
both its failure and the repaired compile against the current published library.

The initial `downstream.py` invocation reported an unknown module because it is quarantined;
its documented `--allow-missing` option reports zero downstream modules and zero users of
the three instance names. Searches of both live and quarantined Lean files found no imports
of this module and no uses of these names beyond the original declarations. No consumer
adaptations or new nodes are necessary.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
