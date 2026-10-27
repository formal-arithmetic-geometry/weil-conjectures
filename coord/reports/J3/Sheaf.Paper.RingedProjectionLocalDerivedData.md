## What changed

Filled `AlgebraicGeometry.Scheme.ProjectionRestriction.localDerivedData_exists` in
`Sheaf.Paper.RingedProjectionLocalDerivedData`. The ordinary direct-image square is
constructed explicitly using `ModuleCat.restrictScalarsCongr` and
`LocalBaseData.coefficient_sections`; it is identity on sections. Restriction of
K-injective complexes uses the existing containing-universe theorem. The exact
ordinary pullback square is localized and its canonical derived mate is used as
the direct-image comparison. The generic cochain normalization proves the precise
representative equation; K-injective resolutions prove invertibility on all derived
objects. Canonical adjunction shift compatibility and the mate counit identity
supply the remaining fields. The existing structure and theorem signature are
unchanged, as are all existing public imports.

Added the proved ordinary normalization lemma
`AlgebraicGeometry.Scheme.ProjectionRestriction.localOrdinaryInverseMate_isIso` in
`Sheaf.Paper.RingedProjectionOrdinarySliceMate`. It identifies the ordinary inverse
mate with the existing `RingedSitePullback.localComparison`, whose invertibility is
already proved for the containing universes. Its private helper is fully proved.
No shared module, definition, instance, attribute or target signature was changed.

Validation: remote `lcompile.py --all` compiled both modules, in 10.5 seconds for
the ordinary helper and 54.5 seconds for the derived package. The sole lint warning
requested an explanatory comment for the heartbeat setting; that comment is added.
The delivery runs the final compilation and preflight checks.

The auxiliary results from smooth purity and smooth base change are generic
localization, adjunction and K-injective tools, not those units' geometric
conclusions. The proper-base-change unit's own route is preserved: this proves its
localized projection comparison package directly from the same specified module
operations and normalized mate, without bypassing the unit's statement or steps.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.ProjectionRestriction.localDerivedData_exists`.
Proved the new ordinary helper
`AlgebraicGeometry.Scheme.ProjectionRestriction.localOrdinaryInverseMate_isIso`.
One original hole closed; zero new holes; zero split-off sorry statements.
Neither delivered Lean file contains a `sorry`. No hollow definition or arbitrary
existence witness was introduced: the ordinary and derived comparisons are explicit
canonical constructions.

## No longer needed

The previous planned dependencies are not used:

- `lem-weil-pbc-ringed-derived-slice-localization`, module
  `Sheaf.Paper.RingedDerivedSliceLocalization`;
- `lem-weil-pbc-ringed-slice-pullback-mate-normalization`, module
  `Sheaf.Paper.RingedSlicePullbackMateNormalization`;
- `lem-weil-pbc-ringed-slice-comparisons-shift`, module
  `Sheaf.Paper.RingedSliceComparisonsShift`.

The actual operations already use the canonical exact localization and right-derived
functors. Localizing the ordinary pullback square and taking its derived mate avoids
choosing fresh arbitrary presentations and then transporting their normalization.
All three planned dependency edges were removed from this node. These shared modules
are not withdrawn, since they may have other consumers. No original Lean import was
removed; the sole original public import remains required by the statements.

## Where the brief, the DAG or earlier work was wrong

The older small-site comparison declarations use equal site-object, hom and
coefficient universes, while these pro-étale sites have object universe `u+1`, hom
universe `u`, and coefficient universe `u+1`. They do not directly specialize to
this item's operations. Existing containing-universe theorems for ordinary pullback
localization and K-injective restriction avoid that mismatch. The DAG's route was
replaced accordingly, with the exact representative and mate normalizations retained.
No statement is disputed and no mathematical assumption was added or removed.

## New nodes

`lem-weil-pbc-ringed-projection-ordinary-slice-mate` records the proved ordinary
inverse-mate normalization lemma. It is strictly the ordinary adjunction step: it
contains no derived comparison, K-injective resolution, representative equation,
shift compatibility or counit identity. Its proof uses the existing proved
`lem-pur-ringed-site-pullback-localization-universes` and the unit mate equation.
The source is Stacks Project, Modules on Sites, Tag 04J0. There are no change records
because no existing definition or statement was changed.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
