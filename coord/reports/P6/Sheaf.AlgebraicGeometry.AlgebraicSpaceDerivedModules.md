## What changed

Filled all four proof holes in `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`.
The structure complex is handled by its actual single-complex cohomology: the inverse
small-model equivalence identifies degree zero with the original unit, and all other
degrees are zero. Proved private helpers construct local presentations of unit and zero
modules using only the already available weak sheafification on chart slices. The empty
free module is zero by its free-Hom universal property. This also handles empty spaces.

Direct-image additivity follows from the existing right-adjoint theorem, additivity of
the inverse equivalence, and sectionwise small-model restriction. Scheme restriction
preserves addition sectionwise. K-injective resolutions follow from the proved
small-site sheaf-of-modules Grothendieck theorem and the existing general resolution theorem.
Added private proof imports for Mathlib additive functors and single-functor homology.
Updated the item's node proof, proof dependencies and proof origin to record these arguments.
All existing statements, definitions, public imports and declaration attributes are preserved.

Validation: the complete item compiled cleanly through `lcompile.py` in 16.9 seconds,
with no diagnostics. Every Lean line is at most 100 characters.

## Proved and sorry left

Closed four of four original holes, all in namespace `AlgebraicGeometry.AlgebraicSpace`:

- `derivedStructure_quasiCoherent`.
- `smallModuleDirectImage_additive`.
- `smallModules_hasKInjectiveResolutions`.
- `smallSchemeRestriction_additive`.

No sorry remains in the item; no holes are added or split off. All four declarations
belong to `def-sfb-space-derived-module-calculus`. The imported small-model equivalence,
original direct-image adjunction and other prerequisite declarations retain their existing
proof obligations; this delivery does not claim to finish those dependencies.

## No longer needed

None. No imports, modules or nodes are withdrawn. The original node had no proof steps
or proof dependencies; the recorded steps now describe the implemented proof. The unit
route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The original node had an empty proof plan despite
four named theorem obligations. Its additivity obligation can use the already stated
right-adjoint property instead of redoing the compatible-chart limit argument.
Some general quasi-coherence helper APIs require full sheafification or binary products
on the large chart site. The available module exposes weak sheafification on each slice;
the new private, completely proved presentation helpers work under precisely those
existing assumptions without adding any new theorem obligations.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
