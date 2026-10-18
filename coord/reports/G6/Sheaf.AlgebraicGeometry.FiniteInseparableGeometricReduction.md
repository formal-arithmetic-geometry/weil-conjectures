## What changed

Repaired the returned delivery by removing the duplicate private theorem
`geometricallyReduced_of_schemeTheoreticallyDominant` from
`Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction`. The assigned module now imports
`Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre` and uses its existing proof. The
existing helper is generalized in place from private to public in the unclaimed module
`Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre`; its proof body and signature are
unchanged. The target theorem and all other declarations are unchanged. The already delivered
`Sheaf.FieldTheory.FiniteFamilyCommonExtension` module remains fully proved and unchanged.

## Proved and sorry left

The assigned target theorem
`AlgebraicGeometry.exists_finite_purelyInseparable_geometricallyReduced_reduction` remains
proved, with zero `sorry`s. The duplicate helper is removed, so this repair adds no holes. The
adapted `geometricallyReduced_of_schemeTheoreticallyDominant` theorem has zero `sorry`s. The
common-field theorem `Algebra.exists_fg_common_field` has zero `sorry`s.

## No longer needed

The local duplicate helper and its proof are no longer needed. The import and proof dependencies
used only by that duplicate helper are pruned from the assigned module; the existing
`RadicialReducedFlatGenericFibre` module supplies the theorem. No other planned dependency or
unit-level route is removed. The finite-family common-extension module remains needed by the
assigned proof. The adaptation is recorded in
`coord/changes/finite-inseparable-geometric-reduction-proof-context.md`.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a private theorem whose statement was already present in the
library. The repair follows the return instruction by exposing the existing theorem in place
and importing it. No statement in the DAG or in `lean/Challenge.lean` is changed.

## New nodes

`lem-pur-finite-family-common-extension` remains the already delivered, fully proved
common-field helper node, with no new `sorry`s in this repair.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
