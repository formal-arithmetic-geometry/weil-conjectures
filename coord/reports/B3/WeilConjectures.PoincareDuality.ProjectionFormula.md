## What changed

Prepared in the sandbox but not delivered: the final dry run is blocked by a delivery-tool failure described below.

Replaced the sole sorry in `WeilConjectures.PoincareDuality.ProjectionFormula` with the compactification argument. The proper projection component is supplied by the new statement-only module `Sheaf.PoincareDuality.ProperProjectionFormulaBounded`. The existing open projection comparison and pullback composition isomorphism supply the other factors; functors preserve their invertibility, and the full-subcategory inclusion reflects invertibility.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleExceptionalProjectionMorphism`. Added one hole in `AlgebraicGeometry.ProEtale.CondensedRing.isIso_properProjection_bounded`, node `lem-pd-condensed-proper-projection-formula`. This is a decomposition: one original hole closed, one proper-case hole added, net zero. The new theorem still needs the precise module-object/ringed-topos comparison and the integral/rational proper projection theorems, whose DAG nodes have no Lean attachment in this checkout. The open and compactification-composition parts are proved here.

## No longer needed

No original imports or modules were pruned. The separately planned node `lem-pd-condensed-open-exceptional-projection-formula` is not imported: this source module already proves the precise `isIso_openImmersionProjectionComparison` instance used by the argument. No global withdrawal is claimed. The only added proof import is `Sheaf.PoincareDuality.ProperProjectionFormulaBounded`; the proof uses its sole declaration. No auxiliary composition module is delivered.

## Where the brief, the DAG or earlier work was wrong

No DAG node in this checkout attaches `WeilConjectures.PoincareDuality.ProjectionFormula`, and its docstrings contain no blueprint tags. The relevant plan is Step 2 of `nt-target-poincare-isiso`. The three proper-case dependencies named in the new node have no Lean attachment here, so the plan cannot yet be applied as Lean declarations. The new theorem isolates just the proper direct-image factor, at A = Di_!K for bounded constructible K,B; it does not restate the exceptional projection theorem or assume its conclusion.

The proper theorem was checked on identity morphisms (the unitor/adjunction identities), zero complexes, and empty source. The existing open formula handles the open factor without a new hole. Integral and unit-ball coefficient presentations both denote valuation-ring coefficients; the finite-field and algebraic-closure cases use the rational proper theorem.

The final dry run reaches preflight and has exactly one failure:
`(a) uncommitted changes in the working tree`. This is a reproducible tool failure.
`/home/ubuntu/weil-launcher/deliver3.py` commits the delivery and then writes tracked
`tools/stage3_gate.py` and `tools/stage3_delivery.py` in its temporary worktree before
invoking preflight. `tools/preflight_delivery.py` checks `git status --porcelain` and
rejects those uncommitted changes. The worker has not edited any delivery tool or
worked around the gate. The earlier change-record format errors have been repaired;
the last dry run has no remaining node, Lean-text, change-record or report error.
Nothing was pushed. Both delivered Lean files compiled together through `lcompile.py
--all` (helper 4.9 seconds, item 57.6 seconds), and the import direction was checked.

## New nodes

`lem-pd-condensed-proper-projection-formula`: proper direct-image projection, with the exact adjoint-of-counit component. Sources are the integral and rational proper projection clauses and the precise module-object comparison used in `nt-target-poincare-isiso` Step 2. The current item's existing declarations and visibility are unchanged. New code lives in its own Sheaf module; no public import is added to the source module.

Change record: `coord/changes/B3-projection-formula-proof-transparency.md`.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
