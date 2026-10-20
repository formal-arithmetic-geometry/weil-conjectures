## What changed

Repaired the DIFFERENT upstream twin in
`Sheaf.AlgebraicGeometry.OpenDerivedLocalizationAdjunction`. The original combined
localization-and-adjunction theorem collides with upstream's narrower theorem of the
same name. Renamed the combined theorem to
`AlgebraicGeometry.open_derived_localizations_and_adjunction`, preserving its entire
type, and proved it by composing upstream
`nonempty_hasDerivedCategory_openSubscheme`, `nonempty_derivedOpenLocalization`, and
`open_derived_localization_adjunction`. The fixed-universe localizations and the
adjunction are all retained. Updated the node attachment and proof; added change
record `coord/changes/open-derived-localization-adjunction-upstream-name.md`.

The original file compiles alone. Adding the upstream module to the original file
reproduced the duplicate-declaration error; the renamed combined result compiles
with the upstream module. No callers require edits: there are no current or
quarantined Sheaf importers; the six upstream consumers listed in the retirement
inventory already use the split upstream interface. No upstream file was edited.

## Proved and sorry left

This is a compatibility repair with zero original holes: 0 holes closed, 0 holes
added, 0 holes left. The complete proof of
`AlgebraicGeometry.open_derived_localizations_and_adjunction` composes the three
existing proved results. The old combined declaration is retired under its colliding
name; the upstream adjunction-only declaration retains that name and its signature.
No new theorem is left with `sorry`; no new nodes are introduced.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`;
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`;
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`;
- `Mathlib.CategoryTheory.Localization.LocallySmall`.

The upstream adjunction module now supplies the first three ingredients, and its
localization-transport helper supplies the smallness argument. Removed the obsolete
local instance attributes. These dependencies remain needed transitively in the
upstream proofs, so no DAG node or module is claimed pruned. All existing node proof
dependencies and parent citations remain valid. The complete combined statement is
still available, so the unit route is preserved. The public import is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief described an unfinished obligation, but the module already
has zero holes. Its actual assignment is the DIFFERENT twin retirement entry: the
upstream sync split the same mathematical statement into three proved results and
reused the old theorem name for the adjunction clause. A plain re-export would drop
the combined API; leaving the old name makes the two modules incompatible. A distinct
name with the unchanged combined type resolves both issues. Empty and full opens
remain covered because the three applied theorems are uniform in every open.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
