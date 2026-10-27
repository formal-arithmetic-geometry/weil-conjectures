## What changed

Filled the proof of `AlgebraicGeometry.prelog_pushout_hom_extension` in
`Sheaf.AlgebraicGeometry.PrelogPushoutHomExtension`. The proof constructs the
sectionwise unit lift, descends the compatible pair map through
`divisorialChartCongruence` using `Con.lift`, applies the supplied sheafification
universal property, and proves structural compatibility and uniqueness. Added the
proof-only import `Sheaf.AlgebraicGeometry.LogUnitSectionLift`.

Added `Sheaf.AlgebraicGeometry.LogUnitSectionLift`, whose named intermediate theorem
isolates the stalkwise-to-sectionwise unit-lift argument.

The removal of two unused public imports is recorded in
`coord/changes/K5-prelog-pushout-unused-imports.md`. The item has no current direct
Lean importers, so no consumer adaptations are necessary.

## Proved and sorry left

The item theorem `AlgebraicGeometry.prelog_pushout_hom_extension` is proved (one
sorry closed). The new theorem
`AlgebraicGeometry.EtaleLogStructure.existsUnique_unit_section_lift` remains as one
named sorry, with node `lem-trf-log-unit-section-lift`; it is the strict intermediate
claim needed to pass from the stalkwise log axiom to sections. No definition contains
sorry.

## No longer needed

The proof does not use the planned fpqc openness, fpqc covering, affine-adjunction,
or representable-descent dependencies. It uses the adopted structure-sheaf theorem
`Scheme.isSheaf_etaleStructurePresheaf` and the generic monoid quotient and
sheafification APIs instead. The removed imports are
`Mathlib.AlgebraicGeometry.Morphisms.Etale`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`,
`Mathlib.AlgebraicGeometry.Sites.Fpqc`,
`Mathlib.AlgebraicGeometry.GammaSpecAdjunction`,
`Mathlib.CategoryTheory.Sites.Sheafification`, and
`Mathlib.CategoryTheory.Sites.PreservesSheafification`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the stalkwise log-unit axiom as if it directly gave
unique lifts on every étale section. That implication is a separate sheaf argument,
so it is split out as `lem-trf-log-unit-section-lift` rather than hidden inside the
extension proof. The planned fpqc descent proof of the multiplicative structure sheaf
is unnecessary because the adopted source library already proves
`Scheme.isSheaf_etaleStructurePresheaf`.

## New nodes

`lem-trf-log-unit-section-lift`: every ring unit section on an étale test scheme has a
unique lift to an étale log structure. Its source is ILO Exposé VI 1.1, printed p.69,
with Stacks Tags 03PT and 03PU for the stalk and conservativity steps. The Lean
statement is in `Sheaf.AlgebraicGeometry.LogUnitSectionLift`.

Change record: `coord/changes/K5-prelog-pushout-unused-imports.md`.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
