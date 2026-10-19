## What changed

The item module is withdrawn as a pruned module. Its only direct consumer,
`Sheaf.Paper.NoetherianPrimePowerSmoothDuality`, is adapted by removing its proof-only
import of `Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals`. Its Noetherian diagonal-integral input is now imported directly from
`Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals`. Its projective-line
normalization already comes from `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` and
`Sheaf.AlgebraicGeometry.ProjectiveLineTrace`; the parent proof uses only Noetherian bases,
so no declaration from the arbitrary-base module is required. The adapted parent also writes `lineAppend` as explicit `Nat.rec` to avoid expensive
recursive-definition elaboration. Its zero and successor tensor maps are identical.
The change record is `coord/changes/noetherian-line-append-recursion.md`.

## Proved and sorry left

No theorem was proved: the withdrawn item had one sorry, `AlgebraicGeometry.Etale.arbitraryBaseP1_integrals`.
The module is pruned because its declarations are not used by the target import closure after
removing the redundant parent import. No new sorry was added. The adapted parent's pre-existing sorry remains in
`AlgebraicGeometry.Etale.NoetherianSmoothDuality.noetherianPrimePowerSmoothDuality`
(node `lem-per-noetherian-prime-power-smooth-duality`). Thus this is pruning, with
0 of 1 holes proved, 1 holed module withdrawn, and 0 split off.

Validation: the required dry run passed (commit `b1d8aa5f74`, CODEX review).
All existing signatures, theorem bodies and public imports are identical after stripping
docstrings and proof-only imports and excluding the documented `lineAppend` value. The sole definition-body rewrite is the explicit structural recursion
in `lineAppend`. Both original recursive equations were checked by `rfl` in
`scratchpad/LineAppendEquations.lean` via `lcompile.py` (55.1 seconds, exit 0).
A source search finds no references to any of the five withdrawn interface declarations
outside the item. The removal follows brief step 8d. The change record
is `coord/changes/withdraw-arbitrary-base-p1-integrals.md`.

## No longer needed

Removed the parent's proof-only import `Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals`
and its Step 2 dependency and obsolete tool approval for
`lem-sp-tower-p1-arbitrary-base-integrals`. It is replaced by the Noetherian integral input
`lem-amb-p1-diagonal-integrals`, already used by the retained `det-sp-p1-adjunction` route.
The new direct generic-tool dependency may need maintainer approval; no approval was added.
Neither item nor parent is a node in a unit realization; no unit statement or step changes.
All Noetherian base-change, affine-space and supported-diagonal normalization clauses stay.

Only `Sheaf.AlgebraicGeometry.ArbitraryBaseP1Integrals` is claimed pruned from the target
closure. None of its dependencies is claimed globally pruned: several are independently used.
The item's full arbitrary-base proof plan and statement remain in its DAG node, with its Lean
attachment removed. The unrelated unformalized `det-sp-tower-p1-adjunction` still needs the
arbitrary-base result; it has no Lean importer, so it does not require keeping this holed module
in the current target import closure. Its unit statement and steps are untouched. Likewise the
unformalized `lem-per-ordinary-smooth-orientation` node is untouched.

The universal-base helper exploration was not delivered. No dependency of the existing
Noetherian adjunction route is removed.

## Where the brief, the DAG or earlier work was wrong

The item was dispatched because it was imported by `NoetherianPrimePowerSmoothDuality`, but that
import was proof-only and the parent proof's hypotheses are all Noetherian. The parent already
uses the Noetherian finite projective-line adjunction and its normalized supported-diagonal
triangle identities. Treating the arbitrary-base theorem as a required dependency duplicated
that route. The arbitrary-base DAG statement and its proof plan remain unchanged; only its Lean
attachment is removed and its proof-origin note records the withdrawal. It remains a planned
input for the separate arbitrary-base tower construction.

The first resumed dry run rejected the inherited profiling output as warnings. Removing
profiling and restoring the original `lineAppend` then timed out at 60 seconds. The
explicit `Nat.rec` avoids that recursive-definition elaboration cost without changing
the tensor maps. No compile limit was raised and no file was split.

Dispatcher metadata: provider HTTP 429 interrupted attempt 1792399240 and its continuation
1792406731. The inherited report recorded a reference reset to 1792407771. At this continuation
the dispatcher-provided `.budget` contains `start = 1792413723.2337408`; this worker
did not edit it and continues under the original session deadline. The launcher
owner should preserve the original clock across provider retries.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
