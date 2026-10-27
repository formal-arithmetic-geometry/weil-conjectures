## What changed

Reduced `AlgebraicGeometry.ProEtale.finiteDuality_locallyClosed_comparison` without
changing its statement or the existing comparison structure. The proof constructs
Noetherianity and quasi-compactness, chooses the actual closed adjoints, proves
boundedness by exact-adjoint t-structure orthogonality, constructs gamma as a counit
transpose, and constructs transport as gamma inverse followed by the image of the
site-comparison unit. It proves the pasted counit and unit-normalization identities.
The existing factorization uniqueness proof is retained.

Moved the comparison coordinates verbatim to `LocallyClosedComparisonCoordinates`
so the new proof steps do not create an import cycle; the parent publicly reexports
all declarations. See `coord/changes/Z9-locally-closed-comparison-coordinates.md`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.finiteDuality_locallyClosed_comparison` by decomposition.
Hole counts: one original hole closed; one new hole added; zero holes remain in the
assigned module. This is a decomposition, with net hole reduction zero.
One split theorem remains:
`AlgebraicGeometry.ProEtale.locallyClosedCounitMate_isIso`
(node `lem-sf-locally-closed-counit-comparison`), asserting only invertibility of the
explicitly constructed canonical mate on bounded constructible inputs.

The relative Hom formula is proved without holes in
`AlgebraicGeometry.ProEtale.locallyClosedRelativeHomIdentity`
(node `lem-sf-locally-closed-relative-hom-identity`); it compiles in 11.7 seconds.
The relocated coordinates and the mate construction also compile. The final
whole-sandbox compile passes all four modules, including the assigned theorem and
its retained factorization theorem.
There are no holes in a definition or private declaration.

## No longer needed

The parent no longer needs the separate closure-realization, closure-comparison-square
or relative-transpose-normalization bundles: its exact-adjoint bound is direct,
its closure etale identification is already constructed, and its relative Hom equation
is a formal consequence of the explicit normalization axiom. The no-longer-directly-used
planned dependencies are `lem-sf-locally-closed-closure-adjoint-realization`,
`lem-sf-locally-closed-closure-comparison-square` and
`lem-sf-locally-closed-relative-transpose-normalization`. Their modules are not withdrawn;
other consumers may still need them. Closed comparison, pullback comparison and derived
immersion normalization remain needed below the component-invertibility step.
No source-library declaration is removed or modified.

Removed unused private imports from the parent and relocated coordinates:

- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`
- `Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Paper.BoundedSiteAdjunctionTranspose`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.SixFunctors.FiniteDualityClosedComparison`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `WeilConjectures.ConstructibleSheaf.Pullback`

## Where the brief, the DAG or earlier work was wrong

The existing closure-realization theorem uses `E : Type u` and ULift coefficients;
the assigned theorem uses `E : Type (u + 1)` and the unlifted coefficient quotient.
It cannot be applied directly. Its geometric and lower-bound clauses can instead be
proved here with Mathlib and the already proved exact-derived-adjunction bound.
The normalization axiom of `FixedComparisonClassAdjunction` gives the relative Hom
identity directly for the literal composite in the statement, so a second independent
closure comparison square is not needed for that field. The blueprint unit route,
target statements, comparison functors and all original definitions are preserved.

## New nodes

`def-sf-locally-closed-comparison-coordinates` records the verbatim relocated definitions.
`lem-sf-locally-closed-counit-comparison` is the strictly smaller geometric assertion
that the constructed mate is invertible; its complete proof plan specifies application
of the existing closed comparison and normalized open comparison.
`lem-sf-locally-closed-relative-hom-identity` records the proved formal Hom calculation
from the counit identity, normalized class adjunction and comparison unit.

Change record: `coord/changes/Z9-locally-closed-comparison-coordinates.md`.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
