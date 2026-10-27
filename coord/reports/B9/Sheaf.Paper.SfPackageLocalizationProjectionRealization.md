## What changed

Proved `sfPackageLocalizationFiniteImage` in
`Sheaf.Paper.SfPackageLocalizationProjectionRealization`. Private proved helpers transport
unique natural recollement boundaries through the normalized adjunction comparisons,
apply a triangulated compact-support functor, and transport finite-Tor conditions through
object isomorphisms. The actual counit, unit, composition comparisons, connecting-map
formula, and all three finite-Tor conclusions are retained. Both empty strata remain
allowed. Added the proof-only import `Sheaf.Paper.FiniteTorStability`.

Updated the item's node proof and proof origin to describe the finite proof. No public
signature, definition, target, or source-library declaration changed.

## Proved and sorry left

Closed one of the original six holes: `sfPackageLocalizationFiniteImage`.
Added no holes. The following five existing holes remain, all attached to
`lem-sf-package-localization-projection-realization`:

- `sfPackageLocalizationIntegralTower`
- `sfPackageLocalizationRationalization`
- `sfPackageLocalizationCommonStages`
- `sfPackageLocalizationWeil_rational`
- `sfPackageLocalizationWeil_common`

The new private helpers are completely proved. This is a proof of the finite refinement
from the existing declared dependencies, not a split into new obligations.

## No longer needed

None. Existing public imports and planned dependencies for the five unfinished refinements
are retained. The finite proof uses the stated recollement, compact-support exactness,
and finite-Tor stability route. No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The finite proof needs explicit instances for the
geometric composites and explicit cancellations of the associator identity components;
these are proof elaboration details and require no interface repair.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
