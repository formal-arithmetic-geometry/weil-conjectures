## What changed

Restored `lean/Sheaf/Targets/PoincareUncurry.lean` from the quarantined source,
keeping its theorem signature and docstrings verbatim. Proved
`AlgebraicGeometry.ProEtale.CondensedRing.uncurry_poincareMap_of_smooth` by specializing
`CategoryTheory.Verdier.uncurry_poincareMap` to the existing two adjunctions,
exceptional projection and smooth purity isomorphism. The canonical maps, purity
normalization and explicit smoothness hypothesis are unchanged.

The existing node records this specialization in `proof`, `proof_deps` and
`proof_origin`; all its other fields are unchanged. The change record is
`coord/changes/T1-poincare-uncurry-restoration.md`. No upstream module is modified.

The required delivery command completed successfully on 2026-10-25 and printed
`DELIVERED Sheaf.Targets.PoincareUncurry at b884585e5e1`. It passed the delivery
compile, axiom checks and server preflight. This report update records that success;
the maintainer's independent review and global build remain subsequent checks.

## Proved and sorry left

Closed the one archived hole:
`AlgebraicGeometry.ProEtale.CondensedRing.uncurry_poincareMap_of_smooth`
(node `nt-target-poincare-uncurry`). Remaining holes in this module: zero.
Added holes: zero. Split-off statements: zero.

## No longer needed

Removed redundant imports:

- `Sheaf.Targets.SmoothPurityQbar`;
- `Sheaf.Targets.PoincareTateBoundedConstructible`;
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`;
- `Mathlib.CategoryTheory.Monoidal.Closed.Basic`;
- `Mathlib.CategoryTheory.Monoidal.Category`.

The remaining public import `WeilConjectures.PoincareDuality.Poincare` supplies
the statement and its proof. The independent target wrappers are unnecessary for
this specialization. The other three imports provide APIs already available through
Poincare. Removed direct proof-dependency edges to `lem-pod-closed-uncurry-laws` and
`def-sfb-monoidal-category`: their calculation is already proved in the abstract
identity. These facts remain used upstream; no declaration or module is withdrawn.
All statement dependencies and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The original quarantine error was a duplicate imported auxiliary declaration.
The current upstream Poincare module has been restored independently and already
contains the required abstract specialization. Its abstract proof performs the
original transpose, naturality and left-unitor calculation, so duplicating that
calculation here is unnecessary.

Previous attempts encountered incompatible published dependency terms at
`isMonoidalClosed_boundedConstructible`. The unchanged wrapper's standalone compile
returned that old cached failure during this attempt; it is not a fresh failure.
The required delivery command subsequently succeeded, so the earlier BLOCKED
assessment is superseded by that completed validation. Historical diagnostics and
the prior report are retained under `scratchpad/`; no compiled artifact, launcher
script, upstream signature or budget metadata was changed to bypass a check.

Mechanical checks confirm the archived signature is identical, the item has no
`sorry` tokens, all Lean lines fit 100 columns, and only the three proof-related
node fields differ. The unit realization is unchanged. Current consumer searches
find no importers or uses of the wrapper in `lean/` or `quarantine/`; the module
is nevertheless restored, with its DAG attachment intact.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
