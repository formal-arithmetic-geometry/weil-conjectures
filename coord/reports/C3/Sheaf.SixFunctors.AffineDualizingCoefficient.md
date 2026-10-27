## What changed

Proved `AlgebraicGeometry.Etale.affine_dualizing_coefficient` in
`Sheaf.SixFunctors.AffineDualizingCoefficient` from the existing normalized ordinary
projection mate and finite Tate scalar normalization. Private proved helpers give
counit transport, uniqueness of the mate and the literal dimension-zero identity.
The theorem signature and all original public declaration signatures are unchanged.

The original eight-clause conclusion is now stored verbatim as the eight fields of
`AffineDualizingCoefficientConclusions`; the assertion retains all four original
premises. This equivalent representation removes an expensive repeated kernel
conversion. The unit and shifted-single definitions reuse definitionally identical
existing named comparisons. These changes and the consumer audit are recorded in
`coord/changes/C3-affine-dualizing-comparison-cache.md`. The existing theorem node
also records the additional conclusion structure, the proof and its actual dependencies.
No source-library files changed and no new nodes or split-off modules were needed.

Added proof imports for the projection mate, finite Tate normalization, canonical
coordinate tower/Tate isomorphism and unbounded identity coherence. Private-import
access exposes the existing generic proved helpers; the Mathlib Small, PNat, quiver
and compactification definition imports support their definitional comparisons.
The unit/shift interface modules are public imports because the public definitions
now refer to them.

## Proved and sorry left

Closed the sole hole in `AlgebraicGeometry.Etale.affine_dualizing_coefficient`
(node `lem-coef-dualizing-affine-space`): 1 of 1 closed, 0 added, 0 split off.
Actual remaining hole count in the delivered module: zero. Every private helper is
proved. Existing imported theorem holes, including
`WeilConjectures.PurityFiniteSetting.finite_tate_scalar_source_normalization`,
remain their separate project items; this is a proof from existing declarations.

The full module compiled cleanly with the default limit in 36.4 seconds. A subsequent
two-file check compiled both this module and its unchanged sole consumer against
the sandbox output. The diagnostic copy of that consumer was removed afterwards;
it is not part of the delivery.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.Paper.ConnectedTateLineEndomorphisms`
- `Sheaf.SecSmoothPurity.LocalizedExtensionZeroLinearDerived`
- `Sheaf.AlgebraicGeometry.PurityAffineLineComponents`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.RingedDerivedPushforwardLinear`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`

This item no longer directly uses `cor-amb-affine-space-adjunction`,
`def-amb-etale-compact-support`, `lem-asd-finite-etale-twist-line`,
`lem-cbc-localized-extension-zero-linear-derived`,
`lem-coef-connected-tate-line-endomorphisms`, `lem-pur-a1-components`,
`lem-pur-derived-change-of-rings`, `lem-pur-ringed-derived-pushforward-linear`,
or `lem-weil-pbc-etale-site-localization-open` as proof dependencies. The existing
projection-mate theorem already proves invertibility of this exact map, so the
connectedness and scalar-endomorphism detection argument is unnecessary here.
Finite Tate scalar source normalization supplies the ordinary generator and shifted
single comparisons. Removed obsolete corresponding top-level tool approvals while
retaining the order of those still used. No declarations or modules withdrawn;
these modules can remain needed transitively or by other parents.

## Where the brief, the DAG or earlier work was wrong

The original plan duplicates an existing proof: the general finite-ring
`ordinaryAffineProjectionAssertion` already handles this specified projection mate,
including its normalization equation. Applying it to the derived tensor unit gives
a shorter route. Its invertibility follows without assuming flatness of B over A.
The identity clause still needs an explicit coherence calculation: merely identifying
the objects with units does not establish the literal identity.

The canonical `CoordinateCounitArrows.towerTateIso` directly gives the needed tower
object identification. The generic right-normal-form import is unnecessary here.
The unit `sk-prop-sf-biduality-general` has no realized statement or step nodes, so
this substitution preserves its recorded route. The same canonical equations cover
r=0, m=n and nonflat n>m. The common annihilator is the positive power l^n, whose
image on Spec k is a unit because l differs from the characteristic.

The nested assertion conjunction caused an expensive kernel conversion. The structure
representation fixes that cause while preserving every clause and premise. The sole
downstream module, `Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization`
(held by G2), uses only the unchanged `affineDualizingTowerComparison`; no forced
adaptation is needed. No target statement is edited; the equivalent assertion
representation is submitted for the independent semantic check with the change record.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
