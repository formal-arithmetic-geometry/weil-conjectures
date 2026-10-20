## What changed

Proved `AlgebraicGeometry.ProEtale.constantTowerTransition` using the canonical
single-object derived unit and the defining unit equation of the existing
coefficient-comparison mate. The existing
`lowerStarCompRestrictScalarsIso` supplies the strict ordinary comparison
without expanding the sheaf constructions. The theorem's signature is unchanged.
Refactored the augmentation as the composite of the two inverse comparisons.
Mathlib's `Iso.trans_symm` is `rfl`, so this preserves the entire isomorphism
definitionally. The change record lists the item and all 40 downstream modules;
only the item directly mentions the augmentation and no consumer adaptation is
needed. Private helpers establish the mate equation, its single-object
specialization, and the degree-zero augmentation identifications. A private
augmentation equation permits the proof to keep its construction locally
irreducible; repeated functor terms are shared through local lets.
Updated the item's proof route in its DAG node. No new public declarations,
modules, or assumptions are introduced.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.ProEtale.constantTowerTransition`: 1 of 1 holes closed.
Added 0 holes, split off 0 statements, and left 0 `sorry`s in this module.
All private helpers are proved. The final module compiled successfully
with `lcompile.py --all`; a separate consumer of its compiled output confirmed
that `#print axioms` lists only `propext`, `Classical.choice`, and `Quot.sound`.
The original proof and audit consumer compiled in 48.0 and 3.1 seconds.
After the definition refactor, the complete file with the delivery probe compiled
in 52.1 seconds; after sharing terms and adding the private augmentation API,
the exact combined compile and audit passed in 44.0 seconds. All public
signatures are unchanged; the augmentation is
definitionally equal to its old construction. The audit consumer is excluded
from the delivery.

## No longer needed

The proof does not import:

- `Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact`
- `Mathlib.CategoryTheory.Limits.Preserves.Finite`
- `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`
- `Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`

The following nodes cease to be direct proof prerequisites for this item:

- `lem-sf-kinjective-derived-map-computation`
- `lem-sf-normalized-derived-comparison-common-resolution`
- `lem-sp-grothendieck-enough-injectives`
- `lem-weil-pbc-bounded-below-injectives-kinjective`
- `lem-weil-pbc-kinjective-hom-derived`
- `lem-weil-proetale-module-direct-image-left-exact`
- `prop-pur-kinjective-resolutions-exist`

The proof uses the already constructed derived functors and their units, rather
than choosing three resolutions and computing comparison maps through them.
The fixed-scalar direct image supplies the left exactness needed by the existing
canonical augmentation. The adopted source-library modules and declarations
remain intact; these dependency removals do not claim that the corresponding
nodes are unused by other targets or by transitive dependencies.

Removed the obsolete top-level `tool_uses` approvals for
`prop-pur-kinjective-resolutions-exist`,
`lem-weil-proetale-module-direct-image-left-exact`,
`lem-sf-kinjective-derived-map-computation`, and
`lem-sf-normalized-derived-comparison-common-resolution`.
The coefficient comparison approval remains. The existing proved tool
`lem-sbc-right-derived-single-zero-unit` supplies precisely the canonical H⁰
normalization needed here; its declaration is imported privately. The DAG proof
records this new dependency for independent review of the shortened route.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original augmentation constructor
was expensive in the combined delivery check; reversing the inverse factors
uses the same data with a cheaper elaboration, as recorded in
`coord/changes/J6-constant-tower-transition-augmentation.md`. The previous
resolution-level plan
is unnecessary because the library already proves the single-unit degree-zero
normalization and the comparison module proves the defining derived-mate unit
equation and identifies the ordinary mate with the identity. Using these
preserves the prescribed augmentation and the actual section map. The blueprint
unit route is unchanged.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
